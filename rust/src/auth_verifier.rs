//! A concrete, pluggable authenticity boundary for UWV4 requests.
//!
//! The caller must supply the pinned context commitment plus the exact
//! document, genesis, `signatureAlgorithm`, `issuer`, `keyEpoch`,
//! `RuntimeAuthV4Kernel.contextSigningBytes`, and signature bytes projected
//! from the Lean-decoded context-bound request. This module deliberately does
//! not parse UWV4 bytes or reconstruct the signing message.
//!
//! Algorithm [`KEYED_BLAKE3_ALGORITHM`] is a keyed BLAKE3 MAC with a 32-byte
//! secret. It is useful for a deployment in which issuers and the verifier
//! share symmetric keys. It is **not** a public-key signature and provides no
//! EUF-CMA claim for independently distributed verification keys. In
//! particular, a successful [`VerificationAcceptance`] says only that the
//! registered key accepted these exact bytes. It does not prove legal identity,
//! key ownership, authorization, membership, nonce freshness, permission to
//! execute, or durable storage.

use std::collections::BTreeMap;

/// UWV4 algorithm tag for the symmetric keyed-BLAKE3 deployment profile.
pub const KEYED_BLAKE3_ALGORITHM: u8 = 1;

/// The exact values presented to an authenticity verifier.
///
/// `signing_bytes` must be Lean's canonical, kind-3
/// `RuntimeAuthV4Kernel.contextSigningBytes`, not the full request (which also
/// contains `signature`). The verifier intentionally does not offer a second
/// Rust implementation of that encoding. Legacy kind-1 `signingBytesV4` is
/// not interchangeable with this context-bound signing domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerificationInput<'a> {
    pub context_commitment: &'a [u8],
    pub document: &'a [u8],
    pub genesis: &'a [u8],
    pub algorithm: u8,
    pub issuer: u64,
    pub key_epoch: u64,
    pub signing_bytes: &'a [u8],
    pub signature: &'a [u8],
}

/// Precise authenticity refusal reasons preserved at the host boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationRefusal {
    UnknownAlgorithm {
        algorithm: u8,
    },
    UnknownContext,
    UnknownDocument,
    UnknownGenesis,
    UnknownIssuer {
        issuer: u64,
    },
    UnknownKeyEpoch {
        issuer: u64,
        key_epoch: u64,
    },
    RevokedKey {
        issuer: u64,
        key_epoch: u64,
    },
    /// The configured registry could not make a decision, for example because
    /// a remote key service was unavailable. This must fail closed.
    RegistryUnavailable,
    BadSignature,
}

/// A trusted host verifier's attestation that it accepted one exact input.
///
/// Construction is public because [`RequestVerifier`] is deliberately
/// pluggable: an external implementation must be able to attest acceptance.
/// Consequently this is an ordinary trusted-boundary receipt, not a capability,
/// formal proof, or unforgeable Rust token. Admission trusts the verifier
/// implementation that constructs it. The hashes bind every exact byte string
/// presented at this stage, but are not authenticators themselves.
/// This receipt carries no authorization or membership conclusion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationAcceptance {
    context_commitment: Vec<u8>,
    document: Vec<u8>,
    genesis: Vec<u8>,
    signing_bytes: Vec<u8>,
    signature: Vec<u8>,
    context_commitment_hash: [u8; 32],
    document_hash: [u8; 32],
    genesis_hash: [u8; 32],
    algorithm: u8,
    issuer: u64,
    key_epoch: u64,
    signing_bytes_hash: [u8; 32],
    signature_hash: [u8; 32],
}

impl VerificationAcceptance {
    /// Attest that a trusted verifier accepted this exact input.
    ///
    /// Calling this constructor performs no verification. It exists for
    /// implementations of [`RequestVerifier`], which are part of the trusted
    /// host boundary.
    pub fn from_verifier_acceptance(input: VerificationInput<'_>) -> Self {
        Self {
            context_commitment: input.context_commitment.to_vec(),
            document: input.document.to_vec(),
            genesis: input.genesis.to_vec(),
            signing_bytes: input.signing_bytes.to_vec(),
            signature: input.signature.to_vec(),
            context_commitment_hash: *blake3::hash(input.context_commitment).as_bytes(),
            document_hash: *blake3::hash(input.document).as_bytes(),
            genesis_hash: *blake3::hash(input.genesis).as_bytes(),
            algorithm: input.algorithm,
            issuer: input.issuer,
            key_epoch: input.key_epoch,
            signing_bytes_hash: *blake3::hash(input.signing_bytes).as_bytes(),
            signature_hash: *blake3::hash(input.signature).as_bytes(),
        }
    }

    /// An unkeyed content hash binding the pinned admission context. The
    /// digest is not an authenticator or proof that the context is available.
    pub fn context_commitment_hash(&self) -> &[u8; 32] {
        &self.context_commitment_hash
    }

    /// An unkeyed content hash binding the exact signed document id.
    pub fn document_hash(&self) -> &[u8; 32] {
        &self.document_hash
    }

    /// An unkeyed content hash binding the exact signed genesis id.
    pub fn genesis_hash(&self) -> &[u8; 32] {
        &self.genesis_hash
    }

    pub fn algorithm(&self) -> u8 {
        self.algorithm
    }

    pub fn issuer(&self) -> u64 {
        self.issuer
    }

    pub fn key_epoch(&self) -> u64 {
        self.key_epoch
    }

    /// An unkeyed content hash that lets later host stages bind this evidence
    /// back to the same signing bytes. The digest is not an authenticator.
    pub fn signing_bytes_hash(&self) -> &[u8; 32] {
        &self.signing_bytes_hash
    }

    /// An unkeyed content hash binding the exact signature bytes which the
    /// verifier accepted. The digest is not an authenticator.
    pub fn signature_hash(&self) -> &[u8; 32] {
        &self.signature_hash
    }

    /// Check that this trusted-boundary receipt names exactly `input`.
    ///
    /// This does not repeat signature verification. It prevents a verifier
    /// implementation from accidentally returning an acceptance receipt for
    /// a different request than the one currently moving through admission.
    pub fn matches_input(&self, input: VerificationInput<'_>) -> bool {
        self.context_commitment == input.context_commitment
            && self.document == input.document
            && self.genesis == input.genesis
            && self.algorithm == input.algorithm
            && self.issuer == input.issuer
            && self.key_epoch == input.key_epoch
            && self.signing_bytes == input.signing_bytes
            && self.signature == input.signature
    }
}

/// Pluggable authenticity verification. Implementations must fail closed.
pub trait RequestVerifier {
    fn verify(
        &self,
        input: VerificationInput<'_>,
    ) -> Result<VerificationAcceptance, VerificationRefusal>;
}

/// A 32-byte keyed-BLAKE3 secret.
///
/// The type intentionally has no `Debug` implementation, avoiding accidental
/// key disclosure in diagnostics. Copies still exist in ordinary process
/// memory; this module makes no locked-memory or zeroization claim.
#[derive(Clone)]
pub struct KeyedBlake3Key([u8; blake3::KEY_LEN]);

impl KeyedBlake3Key {
    pub const fn from_bytes(bytes: [u8; blake3::KEY_LEN]) -> Self {
        Self(bytes)
    }
}

/// A registry's precise key-lookup result before request context is attached.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeyLookupRefusal {
    UnknownContext,
    UnknownDocument,
    UnknownGenesis,
    UnknownIssuer,
    UnknownKeyEpoch,
    Revoked,
    Unavailable,
}

/// Deployment-owned lookup for an issuer's keyed-BLAKE3 secret at one epoch.
pub trait KeyRegistry {
    fn lookup_keyed_blake3(
        &self,
        context_commitment: &[u8],
        document: &[u8],
        genesis: &[u8],
        issuer: u64,
        key_epoch: u64,
    ) -> Result<KeyedBlake3Key, KeyLookupRefusal>;
}

impl<R: KeyRegistry + ?Sized> KeyRegistry for &R {
    fn lookup_keyed_blake3(
        &self,
        context_commitment: &[u8],
        document: &[u8],
        genesis: &[u8],
        issuer: u64,
        key_epoch: u64,
    ) -> Result<KeyedBlake3Key, KeyLookupRefusal> {
        (**self).lookup_keyed_blake3(context_commitment, document, genesis, issuer, key_epoch)
    }
}

/// A deterministic process-local registry suitable for embedded deployments
/// and tests. Durable key lifecycle remains a deployment responsibility.
#[derive(Default)]
pub struct InMemoryKeyRegistry {
    contexts: BTreeMap<
        Vec<u8>,
        BTreeMap<Vec<u8>, BTreeMap<Vec<u8>, BTreeMap<u64, BTreeMap<u64, StoredKey>>>>,
    >,
}

enum StoredKey {
    Active(KeyedBlake3Key),
    Revoked,
}

impl InMemoryKeyRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert or replace one epoch with an active key.
    pub fn insert_key(
        &mut self,
        context_commitment: &[u8],
        document: &[u8],
        genesis: &[u8],
        issuer: u64,
        key_epoch: u64,
        key: KeyedBlake3Key,
    ) {
        self.contexts
            .entry(context_commitment.to_vec())
            .or_default()
            .entry(document.to_vec())
            .or_default()
            .entry(genesis.to_vec())
            .or_default()
            .entry(issuer)
            .or_default()
            .insert(key_epoch, StoredKey::Active(key));
    }

    /// Revoke an existing epoch. Returns `false` when that exact epoch is not
    /// present; it does not create a synthetic issuer or epoch.
    pub fn revoke_key(
        &mut self,
        context_commitment: &[u8],
        document: &[u8],
        genesis: &[u8],
        issuer: u64,
        key_epoch: u64,
    ) -> bool {
        let Some(key) = self
            .contexts
            .get_mut(context_commitment)
            .and_then(|documents| documents.get_mut(document))
            .and_then(|geneses| geneses.get_mut(genesis))
            .and_then(|issuers| issuers.get_mut(&issuer))
            .and_then(|epochs| epochs.get_mut(&key_epoch))
        else {
            return false;
        };
        *key = StoredKey::Revoked;
        true
    }
}

impl KeyRegistry for InMemoryKeyRegistry {
    fn lookup_keyed_blake3(
        &self,
        context_commitment: &[u8],
        document: &[u8],
        genesis: &[u8],
        issuer: u64,
        key_epoch: u64,
    ) -> Result<KeyedBlake3Key, KeyLookupRefusal> {
        let documents = self
            .contexts
            .get(context_commitment)
            .ok_or(KeyLookupRefusal::UnknownContext)?;
        let geneses = documents
            .get(document)
            .ok_or(KeyLookupRefusal::UnknownDocument)?;
        let issuers = geneses
            .get(genesis)
            .ok_or(KeyLookupRefusal::UnknownGenesis)?;
        let epochs = issuers
            .get(&issuer)
            .ok_or(KeyLookupRefusal::UnknownIssuer)?;
        match epochs.get(&key_epoch) {
            None => Err(KeyLookupRefusal::UnknownKeyEpoch),
            Some(StoredKey::Revoked) => Err(KeyLookupRefusal::Revoked),
            Some(StoredKey::Active(key)) => Ok(key.clone()),
        }
    }
}

/// A verifier for the symmetric keyed-BLAKE3 algorithm profile.
pub struct KeyedBlake3Verifier<R> {
    registry: R,
}

impl<R> KeyedBlake3Verifier<R> {
    pub fn new(registry: R) -> Self {
        Self { registry }
    }

    pub fn registry(&self) -> &R {
        &self.registry
    }

    pub fn into_registry(self) -> R {
        self.registry
    }
}

impl<R: KeyRegistry> RequestVerifier for KeyedBlake3Verifier<R> {
    fn verify(
        &self,
        input: VerificationInput<'_>,
    ) -> Result<VerificationAcceptance, VerificationRefusal> {
        if input.algorithm != KEYED_BLAKE3_ALGORITHM {
            return Err(VerificationRefusal::UnknownAlgorithm {
                algorithm: input.algorithm,
            });
        }

        let key = self
            .registry
            .lookup_keyed_blake3(
                input.context_commitment,
                input.document,
                input.genesis,
                input.issuer,
                input.key_epoch,
            )
            .map_err(|refusal| match refusal {
                KeyLookupRefusal::UnknownContext => VerificationRefusal::UnknownContext,
                KeyLookupRefusal::UnknownDocument => VerificationRefusal::UnknownDocument,
                KeyLookupRefusal::UnknownGenesis => VerificationRefusal::UnknownGenesis,
                KeyLookupRefusal::UnknownIssuer => VerificationRefusal::UnknownIssuer {
                    issuer: input.issuer,
                },
                KeyLookupRefusal::UnknownKeyEpoch => VerificationRefusal::UnknownKeyEpoch {
                    issuer: input.issuer,
                    key_epoch: input.key_epoch,
                },
                KeyLookupRefusal::Revoked => VerificationRefusal::RevokedKey {
                    issuer: input.issuer,
                    key_epoch: input.key_epoch,
                },
                KeyLookupRefusal::Unavailable => VerificationRefusal::RegistryUnavailable,
            })?;

        let expected = blake3::keyed_hash(&key.0, input.signing_bytes);
        if !fixed_32_eq(expected.as_bytes(), input.signature) {
            return Err(VerificationRefusal::BadSignature);
        }

        Ok(VerificationAcceptance::from_verifier_acceptance(input))
    }
}

/// Compare a fixed 32-byte expected value with a public-length candidate.
/// Equal-length content comparison accumulates all byte differences before
/// branching. A non-32-byte signature is public malformed input and refuses
/// before content comparison.
fn fixed_32_eq(expected: &[u8; 32], candidate: &[u8]) -> bool {
    if candidate.len() != expected.len() {
        return false;
    }
    let mut difference = 0_u8;
    for index in 0..expected.len() {
        difference |= expected[index] ^ candidate[index];
    }
    difference == 0
}

/// Compute the keyed-BLAKE3 MAC bytes for an already canonical signing
/// message. This helper does not encode a request or assign authority.
pub fn compute_keyed_blake3_mac(
    key: &KeyedBlake3Key,
    signing_bytes: &[u8],
) -> [u8; blake3::OUT_LEN] {
    *blake3::keyed_hash(&key.0, signing_bytes).as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    const ISSUER: u64 = 17;
    const EPOCH: u64 = 2;
    const KEY: KeyedBlake3Key = KeyedBlake3Key::from_bytes([7; blake3::KEY_LEN]);
    const CONTEXT: &[u8] = b"immutable-admission-context";
    const DOCUMENT: &[u8] = b"document-a";
    const GENESIS: &[u8] = b"genesis-a";
    // The verifier treats the message as opaque; callers own domain
    // correctness. This standalone fixture nevertheless pins the context-bound
    // kind-3 domain rather than demonstrating acceptance of a legacy message.
    const SIGNING_BYTES: &[u8] = b"UWV4\x04\x03 exact Lean context signing bytes";

    fn input<'a>(signature: &'a [u8]) -> VerificationInput<'a> {
        VerificationInput {
            context_commitment: CONTEXT,
            document: DOCUMENT,
            genesis: GENESIS,
            algorithm: KEYED_BLAKE3_ALGORITHM,
            issuer: ISSUER,
            key_epoch: EPOCH,
            signing_bytes: SIGNING_BYTES,
            signature,
        }
    }

    #[test]
    fn acceptance_receipt_matches_every_exact_lane_not_only_digests() {
        let signature = compute_keyed_blake3_mac(&KEY, SIGNING_BYTES);
        let original = input(&signature);
        let acceptance = VerificationAcceptance::from_verifier_acceptance(original);
        assert!(acceptance.matches_input(original));

        for changed in [
            VerificationInput {
                context_commitment: b"other-context",
                ..original
            },
            VerificationInput {
                document: b"other-document",
                ..original
            },
            VerificationInput {
                genesis: b"other-genesis",
                ..original
            },
            VerificationInput {
                algorithm: 2,
                ..original
            },
            VerificationInput {
                issuer: ISSUER + 1,
                ..original
            },
            VerificationInput {
                key_epoch: EPOCH + 1,
                ..original
            },
            VerificationInput {
                signing_bytes: b"UWV4\x04\x03 changed",
                ..original
            },
            VerificationInput {
                signature: &[9; 32],
                ..original
            },
        ] {
            assert!(!acceptance.matches_input(changed));
        }
    }

    fn active_registry() -> InMemoryKeyRegistry {
        let mut registry = InMemoryKeyRegistry::new();
        registry.insert_key(CONTEXT, DOCUMENT, GENESIS, ISSUER, EPOCH, KEY.clone());
        registry
    }

    #[test]
    fn exact_mac_accepts_and_evidence_binds_the_input() {
        let signature = compute_keyed_blake3_mac(&KEY, SIGNING_BYTES);
        let verified = KeyedBlake3Verifier::new(active_registry())
            .verify(input(&signature))
            .expect("exact MAC accepts");

        assert_eq!(
            verified.context_commitment_hash(),
            blake3::hash(CONTEXT).as_bytes()
        );
        assert_eq!(verified.document_hash(), blake3::hash(DOCUMENT).as_bytes());
        assert_eq!(verified.genesis_hash(), blake3::hash(GENESIS).as_bytes());
        assert_eq!(verified.algorithm(), KEYED_BLAKE3_ALGORITHM);
        assert_eq!(verified.issuer(), ISSUER);
        assert_eq!(verified.key_epoch(), EPOCH);
        assert_eq!(
            verified.signing_bytes_hash(),
            blake3::hash(SIGNING_BYTES).as_bytes()
        );
        assert_eq!(
            verified.signature_hash(),
            blake3::hash(&signature).as_bytes()
        );
    }

    #[test]
    fn unknown_algorithm_is_distinct_and_precedes_lookup() {
        let verifier = KeyedBlake3Verifier::new(InMemoryKeyRegistry::new());
        let refusal = verifier.verify(VerificationInput {
            context_commitment: CONTEXT,
            document: DOCUMENT,
            genesis: GENESIS,
            algorithm: 99,
            issuer: ISSUER,
            key_epoch: EPOCH,
            signing_bytes: SIGNING_BYTES,
            signature: &[],
        });
        assert_eq!(
            refusal,
            Err(VerificationRefusal::UnknownAlgorithm { algorithm: 99 })
        );
    }

    #[test]
    fn unknown_issuer_and_epoch_are_distinct() {
        let signature = compute_keyed_blake3_mac(&KEY, SIGNING_BYTES);
        let mut registry = InMemoryKeyRegistry::new();
        registry.insert_key(CONTEXT, DOCUMENT, GENESIS, ISSUER + 1, EPOCH, KEY.clone());
        let verifier = KeyedBlake3Verifier::new(registry);
        assert_eq!(
            verifier.verify(input(&signature)),
            Err(VerificationRefusal::UnknownIssuer { issuer: ISSUER })
        );

        let mut registry = InMemoryKeyRegistry::new();
        registry.insert_key(CONTEXT, DOCUMENT, GENESIS, ISSUER, EPOCH + 1, KEY.clone());
        assert_eq!(
            KeyedBlake3Verifier::new(registry).verify(input(&signature)),
            Err(VerificationRefusal::UnknownKeyEpoch {
                issuer: ISSUER,
                key_epoch: EPOCH,
            })
        );
    }

    #[test]
    fn context_document_and_genesis_are_distinct_lookup_scopes() {
        let signature = compute_keyed_blake3_mac(&KEY, SIGNING_BYTES);
        let verifier = KeyedBlake3Verifier::new(active_registry());

        assert_eq!(
            verifier.verify(VerificationInput {
                context_commitment: b"other-context",
                ..input(&signature)
            }),
            Err(VerificationRefusal::UnknownContext)
        );
        assert_eq!(
            verifier.verify(VerificationInput {
                document: b"other-document",
                ..input(&signature)
            }),
            Err(VerificationRefusal::UnknownDocument)
        );
        assert_eq!(
            verifier.verify(VerificationInput {
                genesis: b"other-genesis",
                ..input(&signature)
            }),
            Err(VerificationRefusal::UnknownGenesis)
        );
    }

    #[test]
    fn revoked_key_and_unavailable_registry_fail_closed() {
        let signature = compute_keyed_blake3_mac(&KEY, SIGNING_BYTES);
        let mut registry = active_registry();
        assert!(registry.revoke_key(CONTEXT, DOCUMENT, GENESIS, ISSUER, EPOCH));
        assert_eq!(
            KeyedBlake3Verifier::new(registry).verify(input(&signature)),
            Err(VerificationRefusal::RevokedKey {
                issuer: ISSUER,
                key_epoch: EPOCH,
            })
        );

        struct Unavailable;
        impl KeyRegistry for Unavailable {
            fn lookup_keyed_blake3(
                &self,
                _context_commitment: &[u8],
                _document: &[u8],
                _genesis: &[u8],
                _issuer: u64,
                _key_epoch: u64,
            ) -> Result<KeyedBlake3Key, KeyLookupRefusal> {
                Err(KeyLookupRefusal::Unavailable)
            }
        }

        assert_eq!(
            KeyedBlake3Verifier::new(Unavailable).verify(input(&signature)),
            Err(VerificationRefusal::RegistryUnavailable)
        );
    }

    #[test]
    fn changed_message_signature_or_length_is_bad_signature() {
        let signature = compute_keyed_blake3_mac(&KEY, SIGNING_BYTES);
        let verifier = KeyedBlake3Verifier::new(active_registry());

        let mut changed_first = signature;
        changed_first[0] ^= 1;
        assert_eq!(
            verifier.verify(input(&changed_first)),
            Err(VerificationRefusal::BadSignature)
        );
        let mut changed_last = signature;
        changed_last[31] ^= 1;
        assert_eq!(
            verifier.verify(input(&changed_last)),
            Err(VerificationRefusal::BadSignature)
        );
        assert_eq!(
            verifier.verify(input(&signature[..31])),
            Err(VerificationRefusal::BadSignature)
        );
        let mut too_long = signature.to_vec();
        too_long.push(0);
        assert_eq!(
            verifier.verify(input(&too_long)),
            Err(VerificationRefusal::BadSignature)
        );
        assert_eq!(
            verifier.verify(VerificationInput {
                signing_bytes: b"different canonical bytes",
                ..input(&signature)
            }),
            Err(VerificationRefusal::BadSignature)
        );
    }
}
