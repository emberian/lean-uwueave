//! Narrow host types for Lean-owned authenticated FORMAT-v4 syntax and
//! context-bound admission projection.
//!
//! This module performs no request decoding, signature verification, nonce
//! decision, authorization, membership decision, execution, or storage. It
//! interprets the legacy kind-1 syntax checkpoint and the kind-4 response from
//! Lean's kind-3 projection endpoint. Accepted bytes were decoded, checked,
//! and projected by Lean under the caller's explicit bound. The public Rust
//! structs are ordinary forgeable data, not evidence that the kernel accepted
//! a request; admission callers must enter through the raw-request function.

use crate::ffi;

/// A precise syntactic refusal from the Lean-owned bounded UWV4 decoder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeAuthV4DecodeRefusal {
    TooLarge,
    BadMagic,
    UnsupportedVersion,
    WrongKind,
    Malformed,
}

/// The complete result of the narrow syntax checkpoint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeAuthV4DecodeOutcome {
    /// Lean accepted and re-encoded exactly one canonical signed-move request.
    /// These bytes have not been shape-checked, authenticated, authorized,
    /// executed, or persisted.
    Accepted {
        canonical_request: Vec<u8>,
    },
    Refused(RuntimeAuthV4DecodeRefusal),
}

/// Bound and canonically decode one UWV4 signed-move request in Lean.
///
/// `maximum_bytes` controls entry into the logical parser. Host allocation of
/// `input` has already happened and is not covered by that logical bound.
pub fn decode_runtime_auth_v4_canonical(
    maximum_bytes: usize,
    input: &[u8],
) -> RuntimeAuthV4DecodeOutcome {
    // This duplicates Lean's logical bound deliberately: crossing the FFI
    // would first copy/allocate the input in Lean, so the kernel's check alone
    // cannot protect host resources.
    if input.len() > maximum_bytes {
        return RuntimeAuthV4DecodeOutcome::Refused(RuntimeAuthV4DecodeRefusal::TooLarge);
    }
    let output = ffi::runtime_auth_v4_decode_canonical(maximum_bytes, input);
    let (&tag, payload) = output
        .split_first()
        .expect("RuntimeAuthV4 kernel returned an empty response");
    match tag {
        0 => {
            assert!(
                !payload.is_empty(),
                "RuntimeAuthV4 kernel accepted without canonical request bytes"
            );
            RuntimeAuthV4DecodeOutcome::Accepted {
                canonical_request: payload.to_vec(),
            }
        }
        1 => refusal(payload, RuntimeAuthV4DecodeRefusal::TooLarge),
        2 => refusal(payload, RuntimeAuthV4DecodeRefusal::BadMagic),
        3 => refusal(payload, RuntimeAuthV4DecodeRefusal::UnsupportedVersion),
        4 => refusal(payload, RuntimeAuthV4DecodeRefusal::WrongKind),
        5 => refusal(payload, RuntimeAuthV4DecodeRefusal::Malformed),
        other => panic!("RuntimeAuthV4 kernel returned unknown result tag {other}"),
    }
}

fn refusal(payload: &[u8], reason: RuntimeAuthV4DecodeRefusal) -> RuntimeAuthV4DecodeOutcome {
    assert!(
        payload.is_empty(),
        "RuntimeAuthV4 refusal unexpectedly carried payload bytes"
    );
    RuntimeAuthV4DecodeOutcome::Refused(reason)
}

/// A stable id paired with the request-local index projected by Lean.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeAuthV4NodeRef {
    pub stable_id: Vec<u8>,
    pub kernel_index: u64,
}

/// The complete neutral projection of one canonical, shape-valid kind-3
/// admission request. Authenticity and every later policy decision remain
/// outside this type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeAuthV4AdmissionProjection {
    pub canonical_request: Vec<u8>,
    pub signing_bytes: Vec<u8>,
    pub signature_algorithm: u8,
    pub signature: Vec<u8>,
    pub document: Vec<u8>,
    pub genesis: Vec<u8>,
    pub context_commitment: Vec<u8>,
    pub issuer: u64,
    pub key_epoch: u64,
    pub nonce: Vec<u8>,
    pub operation_id: Vec<u8>,
    pub lamport: u64,
    pub child: RuntimeAuthV4NodeRef,
    pub destination: Option<RuntimeAuthV4NodeRef>,
    pub exec_replica: u64,
    pub exec_child: u64,
    pub exec_destination: Option<u64>,
    pub exec_cite: u64,
}

/// A semantic shape refusal made by the Lean admission projection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeAuthV4ShapeRefusal {
    EmptyDocument,
    EmptyGenesis,
    EmptyContextCommitment,
    EmptyNonce,
    EmptyOperationId,
    EmptyChildId,
    EmptyDestinationId,
    EmptySignature,
}

/// A host-word representability refusal made by Lean.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeAuthV4HostWidthRefusal {
    ChildIndexTooLarge,
    DestinationIndexTooLarge,
    CiteTooLarge,
}

/// A precise refusal from the Lean-owned kind-3 admission projection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeAuthV4AdmissionRefusal {
    Decode(RuntimeAuthV4DecodeRefusal),
    Shape(RuntimeAuthV4ShapeRefusal),
    HostWidth(RuntimeAuthV4HostWidthRefusal),
}

/// Result of bounded canonical decoding and neutral projection in Lean.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeAuthV4AdmissionOutcome {
    Accepted(RuntimeAuthV4AdmissionProjection),
    Refused(RuntimeAuthV4AdmissionRefusal),
    /// The native kernel returned bytes outside its proved response grammar or
    /// an accepted projection violated a redundant invariant.
    KernelContractViolation,
}

/// Project a context-bound (kind-3) UWV4 admission request in Lean.
///
/// This host code parses only Lean's kind-4 *response*. It does not parse the
/// request, verify its signature, decide nonce freshness, resolve stable ids,
/// authorize, execute, or persist. The preflight length check intentionally
/// duplicates Lean's logical bound because the FFI copy happens first.
pub fn project_runtime_auth_v4_admission(
    maximum_bytes: usize,
    input: &[u8],
) -> RuntimeAuthV4AdmissionOutcome {
    if input.len() > maximum_bytes {
        return RuntimeAuthV4AdmissionOutcome::Refused(RuntimeAuthV4AdmissionRefusal::Decode(
            RuntimeAuthV4DecodeRefusal::TooLarge,
        ));
    }
    interpret_admission_response(&ffi::runtime_auth_v4_project_admission(
        maximum_bytes,
        input,
    ))
}

const ADMISSION_RESPONSE_PREFIX: &[u8] = b"UWV4\x04\x04";

fn interpret_admission_response(bytes: &[u8]) -> RuntimeAuthV4AdmissionOutcome {
    let mut cursor = ResponseCursor::new(bytes);
    if !cursor.take_exact(ADMISSION_RESPONSE_PREFIX) {
        return RuntimeAuthV4AdmissionOutcome::KernelContractViolation;
    }
    let Some(outcome_tag) = cursor.byte() else {
        return RuntimeAuthV4AdmissionOutcome::KernelContractViolation;
    };
    if outcome_tag != 0 {
        let Some(reason) = admission_refusal(outcome_tag) else {
            return RuntimeAuthV4AdmissionOutcome::KernelContractViolation;
        };
        return if cursor.at_end() {
            RuntimeAuthV4AdmissionOutcome::Refused(reason)
        } else {
            RuntimeAuthV4AdmissionOutcome::KernelContractViolation
        };
    }

    let Some(projection) = parse_projection(&mut cursor) else {
        return RuntimeAuthV4AdmissionOutcome::KernelContractViolation;
    };
    if !cursor.at_end() || !projection_invariants_hold(&projection) {
        RuntimeAuthV4AdmissionOutcome::KernelContractViolation
    } else {
        RuntimeAuthV4AdmissionOutcome::Accepted(projection)
    }
}

fn admission_refusal(tag: u8) -> Option<RuntimeAuthV4AdmissionRefusal> {
    use RuntimeAuthV4AdmissionRefusal::{Decode, HostWidth, Shape};
    Some(match tag {
        1 => Decode(RuntimeAuthV4DecodeRefusal::TooLarge),
        2 => Decode(RuntimeAuthV4DecodeRefusal::BadMagic),
        3 => Decode(RuntimeAuthV4DecodeRefusal::UnsupportedVersion),
        4 => Decode(RuntimeAuthV4DecodeRefusal::WrongKind),
        5 => Decode(RuntimeAuthV4DecodeRefusal::Malformed),
        6 => Shape(RuntimeAuthV4ShapeRefusal::EmptyDocument),
        7 => Shape(RuntimeAuthV4ShapeRefusal::EmptyGenesis),
        8 => Shape(RuntimeAuthV4ShapeRefusal::EmptyContextCommitment),
        9 => Shape(RuntimeAuthV4ShapeRefusal::EmptyNonce),
        10 => Shape(RuntimeAuthV4ShapeRefusal::EmptyOperationId),
        11 => Shape(RuntimeAuthV4ShapeRefusal::EmptyChildId),
        12 => Shape(RuntimeAuthV4ShapeRefusal::EmptyDestinationId),
        13 => Shape(RuntimeAuthV4ShapeRefusal::EmptySignature),
        14 => HostWidth(RuntimeAuthV4HostWidthRefusal::ChildIndexTooLarge),
        15 => HostWidth(RuntimeAuthV4HostWidthRefusal::DestinationIndexTooLarge),
        16 => HostWidth(RuntimeAuthV4HostWidthRefusal::CiteTooLarge),
        _ => return None,
    })
}

fn parse_projection(cursor: &mut ResponseCursor<'_>) -> Option<RuntimeAuthV4AdmissionProjection> {
    Some(RuntimeAuthV4AdmissionProjection {
        canonical_request: cursor.field_bytes(161)?,
        signing_bytes: cursor.field_bytes(162)?,
        signature_algorithm: cursor.field_byte(163)?,
        signature: cursor.field_bytes(164)?,
        document: cursor.field_bytes(165)?,
        genesis: cursor.field_bytes(166)?,
        context_commitment: cursor.field_bytes(167)?,
        issuer: cursor.field_u64(168)?,
        key_epoch: cursor.field_u64(169)?,
        nonce: cursor.field_bytes(170)?,
        operation_id: cursor.field_bytes(171)?,
        lamport: cursor.field_u64(172)?,
        child: cursor.field_node_ref(173)?,
        destination: cursor.field_optional_node_ref(174)?,
        exec_replica: cursor.field_u64(175)?,
        exec_child: cursor.field_u64(176)?,
        exec_destination: cursor.field_optional_u64(177)?,
        exec_cite: cursor.field_u64(178)?,
    })
}

fn projection_invariants_hold(p: &RuntimeAuthV4AdmissionProjection) -> bool {
    !p.canonical_request.is_empty()
        && !p.signing_bytes.is_empty()
        && !p.signature.is_empty()
        && !p.document.is_empty()
        && !p.genesis.is_empty()
        && !p.context_commitment.is_empty()
        && !p.nonce.is_empty()
        && !p.operation_id.is_empty()
        && !p.child.stable_id.is_empty()
        && p.destination
            .as_ref()
            .is_none_or(|destination| !destination.stable_id.is_empty())
        && p.issuer == p.exec_replica
        && p.child.kernel_index == p.exec_child
        && p.destination.as_ref().map(|node| node.kernel_index) == p.exec_destination
        && p.exec_destination
            .is_none_or(|index| index <= i64::MAX as u64)
}

struct ResponseCursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> ResponseCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn at_end(&self) -> bool {
        self.offset == self.bytes.len()
    }

    fn byte(&mut self) -> Option<u8> {
        let byte = *self.bytes.get(self.offset)?;
        self.offset += 1;
        Some(byte)
    }

    fn take_exact(&mut self, expected: &[u8]) -> bool {
        let Some(end) = self.offset.checked_add(expected.len()) else {
            return false;
        };
        if self.bytes.get(self.offset..end) != Some(expected) {
            return false;
        }
        self.offset = end;
        true
    }

    /// Decode Lean's canonical unary Nat (`1^n 0`) into a host `usize`.
    fn nat_usize(&mut self) -> Option<usize> {
        let mut value = 0usize;
        loop {
            match self.byte()? {
                0 => return Some(value),
                1 => value = value.checked_add(1)?,
                _ => return None,
            }
        }
    }

    fn nat_u64(&mut self) -> Option<u64> {
        let mut value = 0u64;
        loop {
            match self.byte()? {
                0 => return Some(value),
                1 => value = value.checked_add(1)?,
                _ => return None,
            }
        }
    }

    fn bytes(&mut self) -> Option<Vec<u8>> {
        let len = self.nat_usize()?;
        let end = self.offset.checked_add(len)?;
        let value = self.bytes.get(self.offset..end)?.to_vec();
        self.offset = end;
        Some(value)
    }

    fn expect_tag(&mut self, expected: u8) -> Option<()> {
        (self.byte()? == expected).then_some(())
    }

    fn field_bytes(&mut self, tag: u8) -> Option<Vec<u8>> {
        self.expect_tag(tag)?;
        self.bytes()
    }

    fn field_byte(&mut self, tag: u8) -> Option<u8> {
        self.expect_tag(tag)?;
        self.byte()
    }

    fn field_u64(&mut self, tag: u8) -> Option<u64> {
        self.expect_tag(tag)?;
        self.nat_u64()
    }

    fn node_ref(&mut self) -> Option<RuntimeAuthV4NodeRef> {
        Some(RuntimeAuthV4NodeRef {
            stable_id: self.field_bytes(49)?,
            kernel_index: self.field_u64(50)?,
        })
    }

    fn field_node_ref(&mut self, tag: u8) -> Option<RuntimeAuthV4NodeRef> {
        self.expect_tag(tag)?;
        self.node_ref()
    }

    fn field_optional_node_ref(&mut self, tag: u8) -> Option<Option<RuntimeAuthV4NodeRef>> {
        self.expect_tag(tag)?;
        match self.byte()? {
            0 => Some(None),
            1 => Some(Some(self.node_ref()?)),
            _ => None,
        }
    }

    fn field_optional_u64(&mut self, tag: u8) -> Option<Option<u64>> {
        self.expect_tag(tag)?;
        match self.byte()? {
            0 => Some(None),
            1 => Some(Some(self.nat_u64()?)),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::Path;
    use std::process::Command;

    fn unary(value: u64) -> Vec<u8> {
        let mut bytes = vec![1; usize::try_from(value).unwrap()];
        bytes.push(0);
        bytes
    }

    fn push_bytes(output: &mut Vec<u8>, tag: u8, value: &[u8]) {
        output.push(tag);
        output.extend(unary(value.len() as u64));
        output.extend(value);
    }

    fn push_nat(output: &mut Vec<u8>, tag: u8, value: u64) {
        output.push(tag);
        output.extend(unary(value));
    }

    fn accepted_response(exec_child: u64) -> Vec<u8> {
        let mut output = ADMISSION_RESPONSE_PREFIX.to_vec();
        output.push(0);
        push_bytes(&mut output, 161, b"canonical");
        push_bytes(&mut output, 162, b"signing");
        output.extend([163, 1]);
        push_bytes(&mut output, 164, b"signature");
        push_bytes(&mut output, 165, b"document");
        push_bytes(&mut output, 166, b"genesis");
        push_bytes(&mut output, 167, b"context");
        push_nat(&mut output, 168, 7);
        push_nat(&mut output, 169, 8);
        push_bytes(&mut output, 170, b"nonce");
        push_bytes(&mut output, 171, b"operation");
        push_nat(&mut output, 172, 9);
        output.push(173);
        push_bytes(&mut output, 49, b"child");
        push_nat(&mut output, 50, 2);
        output.extend([174, 1]);
        push_bytes(&mut output, 49, b"destination");
        push_nat(&mut output, 50, 3);
        push_nat(&mut output, 175, 7);
        push_nat(&mut output, 176, exec_child);
        output.extend([177, 1]);
        output.extend(unary(3));
        push_nat(&mut output, 178, 4);
        output
    }

    #[test]
    fn admission_host_bound_refuses_before_ffi() {
        assert_eq!(
            project_runtime_auth_v4_admission(0, &[0]),
            RuntimeAuthV4AdmissionOutcome::Refused(RuntimeAuthV4AdmissionRefusal::Decode(
                RuntimeAuthV4DecodeRefusal::TooLarge
            ))
        );
    }

    #[test]
    fn response_refusals_are_exact_and_trailing_bytes_violate_contract() {
        for tag in 1..=16 {
            let mut response = ADMISSION_RESPONSE_PREFIX.to_vec();
            response.push(tag);
            assert!(matches!(
                interpret_admission_response(&response),
                RuntimeAuthV4AdmissionOutcome::Refused(_)
            ));
            response.push(0);
            assert_eq!(
                interpret_admission_response(&response),
                RuntimeAuthV4AdmissionOutcome::KernelContractViolation
            );
        }
    }

    #[test]
    fn response_rejects_bad_framing_unknown_tags_and_noncanonical_unary() {
        assert_eq!(
            interpret_admission_response(b"UWV4\x04\x03\x01"),
            RuntimeAuthV4AdmissionOutcome::KernelContractViolation
        );
        assert_eq!(
            interpret_admission_response(b"UWV4\x04\x04\x11"),
            RuntimeAuthV4AdmissionOutcome::KernelContractViolation
        );
        let mut malformed = ADMISSION_RESPONSE_PREFIX.to_vec();
        malformed.extend_from_slice(&[0, 161, 2]);
        assert_eq!(
            interpret_admission_response(&malformed),
            RuntimeAuthV4AdmissionOutcome::KernelContractViolation
        );
    }

    #[test]
    fn accepted_projection_maps_every_field_and_checks_redundancy() {
        let RuntimeAuthV4AdmissionOutcome::Accepted(projection) =
            interpret_admission_response(&accepted_response(2))
        else {
            panic!("valid response was not accepted")
        };
        assert_eq!(projection.signature_algorithm, 1);
        assert_eq!(projection.canonical_request, b"canonical");
        assert_eq!(projection.signing_bytes, b"signing");
        assert_eq!(projection.signature, b"signature");
        assert_eq!(projection.document, b"document");
        assert_eq!(projection.genesis, b"genesis");
        assert_eq!(projection.context_commitment, b"context");
        assert_eq!(projection.issuer, 7);
        assert_eq!(projection.key_epoch, 8);
        assert_eq!(projection.nonce, b"nonce");
        assert_eq!(projection.operation_id, b"operation");
        assert_eq!(projection.lamport, 9);
        assert_eq!(projection.child.stable_id, b"child");
        assert_eq!(projection.child.kernel_index, 2);
        let destination = projection.destination.unwrap();
        assert_eq!(destination.stable_id, b"destination");
        assert_eq!(destination.kernel_index, 3);
        assert_eq!(projection.exec_replica, 7);
        assert_eq!(projection.exec_child, 2);
        assert_eq!(projection.exec_destination, Some(3));
        assert_eq!(projection.exec_cite, 4);

        assert_eq!(
            interpret_admission_response(&accepted_response(99)),
            RuntimeAuthV4AdmissionOutcome::KernelContractViolation
        );
    }

    fn lean_corpus(arguments: &[&str]) -> Vec<u8> {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("crate is directly below repository root");
        let output = Command::new("lake")
            .args([
                "env",
                "lean",
                "--run",
                "rust/tests/support/RuntimeAuthV4AdmissionCorpus.lean",
            ])
            .args(arguments)
            .current_dir(repository)
            .output()
            .expect("launch Lean admission corpus");
        assert!(
            output.status.success(),
            "Lean corpus stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        output.stdout
    }

    #[test]
    fn real_lean_endpoint_projects_lean_owned_request() {
        let signing_bytes = lean_corpus(&["signing", "base"]);
        let signature_path = std::env::temp_dir().join(format!(
            "uwueave-auth-projection-unit-{}.bin",
            std::process::id()
        ));
        let _ = fs::remove_file(&signature_path);
        fs::write(&signature_path, b"test-signature").expect("write signature fixture");
        let request = lean_corpus(&[
            "request",
            "base",
            signature_path.to_str().expect("UTF-8 temp path"),
        ]);
        let _ = fs::remove_file(&signature_path);

        let RuntimeAuthV4AdmissionOutcome::Accepted(projection) =
            project_runtime_auth_v4_admission(request.len(), &request)
        else {
            panic!("real Lean endpoint refused its own canonical fixture")
        };
        assert_eq!(projection.canonical_request, request);
        assert_eq!(projection.signing_bytes, signing_bytes);
        assert_eq!(projection.signature, b"test-signature");
        assert_eq!(projection.document, [1, 2]);
        assert_eq!(projection.genesis, [3, 4]);
        assert_eq!(projection.context_commitment, [30, 31]);
        assert_eq!(projection.issuer, projection.exec_replica);
        assert_eq!(projection.child.kernel_index, projection.exec_child);
        assert_eq!(
            projection
                .destination
                .as_ref()
                .map(|node| node.kernel_index),
            projection.exec_destination
        );
    }
}
