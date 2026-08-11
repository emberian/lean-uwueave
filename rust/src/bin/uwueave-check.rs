//! uwueave-check — look up merge-safety verdicts for a replicated schema.
//!
//! This tool makes the Lean verdict catalog in `Uwueave/` usable without
//! opening Lean: you describe your replicated fields and the invariants you
//! care about in a tiny line-based schema, and it answers — per invariant —
//! whether the merge can break it, citing the exact machine-checked theorem
//! that settles the question.
//!
//! It is a LOOKUP TABLE, not a checker. Every (shape, kind) entry below is
//! annotated with the theorem it cites, and the unit tests verify, against
//! the actual Lean sources, that the table cannot disagree with them:
//!   - every cited file exists and defines the cited theorem (outside
//!     comments, resolved through the file's real namespace structure to a
//!     fully-qualified name — display names are not keys);
//!   - each citation's ledger status matches docs/MAP.md's keystone ledger
//!     (the curated public-surface list), in BOTH directions: citing an
//!     unlisted theorem as a keystone fails the suite, and so does keeping an
//!     `[unlisted]` marker after the ledger gains the row — the catalog
//!     cannot silently outrun its receipts, nor sit on them;
//!   - each verdict's direction matches the cited statements as written in
//!     the Lean: a FREE row may not cite a `¬ IConfluent` theorem and must
//!     cite a positive one, an ESCALATES row must cite a negation, a SEAM row
//!     must cite both the `SegmentedIConfluent` seam and the global negation.
//! Pairs the Lean development does not settle are reported UNCLASSIFIED —
//! never guessed.
//!
//! Zero dependencies: std only.

use std::env;
use std::fs;
use std::process;

// ============================================================================
// Shapes and invariant kinds
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shape {
    GSet,
    GCounter,
    PnCounter,
    Lww,
    MvReg,
    OrSet,
    ClSet,
    Escrow,
    CausalDag,
    MoveLog,
}

const ALL_SHAPES: [Shape; 10] = [
    Shape::GSet,
    Shape::GCounter,
    Shape::PnCounter,
    Shape::Lww,
    Shape::MvReg,
    Shape::OrSet,
    Shape::ClSet,
    Shape::Escrow,
    Shape::CausalDag,
    Shape::MoveLog,
];

impl Shape {
    fn token(self) -> &'static str {
        match self {
            Shape::GSet => "gset",
            Shape::GCounter => "gcounter",
            Shape::PnCounter => "pncounter",
            Shape::Lww => "lww",
            Shape::MvReg => "mvreg",
            Shape::OrSet => "orset",
            Shape::ClSet => "clset",
            Shape::Escrow => "escrow",
            Shape::CausalDag => "causal-dag",
            Shape::MoveLog => "movelog",
        }
    }

    fn parse(s: &str) -> Option<Shape> {
        ALL_SHAPES.iter().copied().find(|sh| sh.token() == s)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Member,
    NotMember,
    LowerBound,
    Ceiling,
    Unique,
    Mutex,
    Balance,
    PerReplicaQuota,
    Acyclic,
    ActivePath,
    CrossField,
}

const ALL_KINDS: [Kind; 11] = [
    Kind::Member,
    Kind::NotMember,
    Kind::LowerBound,
    Kind::Ceiling,
    Kind::Unique,
    Kind::Mutex,
    Kind::Balance,
    Kind::PerReplicaQuota,
    Kind::Acyclic,
    Kind::ActivePath,
    Kind::CrossField,
];

impl Kind {
    fn token(self) -> &'static str {
        match self {
            Kind::Member => "member",
            Kind::NotMember => "not-member",
            Kind::LowerBound => "lower-bound",
            Kind::Ceiling => "ceiling",
            Kind::Unique => "unique",
            Kind::Mutex => "mutex",
            Kind::Balance => "balance",
            Kind::PerReplicaQuota => "per-replica-quota",
            Kind::Acyclic => "acyclic",
            Kind::ActivePath => "active-path",
            Kind::CrossField => "cross-field",
        }
    }

    fn parse(s: &str) -> Option<Kind> {
        ALL_KINDS.iter().copied().find(|k| k.token() == s)
    }
}

fn shape_tokens_joined() -> String {
    ALL_SHAPES.iter().map(|s| s.token()).collect::<Vec<_>>().join(", ")
}

fn kind_tokens_joined() -> String {
    ALL_KINDS.iter().map(|k| k.token()).collect::<Vec<_>>().join(", ")
}

// ============================================================================
// Verdicts and citations
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Free,
    Escalates,
    Seam,
    Pattern,
}

impl Verdict {
    fn label(self) -> &'static str {
        match self {
            Verdict::Free => "FREE",
            Verdict::Escalates => "ESCALATES",
            Verdict::Seam => "SEAM",
            Verdict::Pattern => "PATTERN",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Cite {
    thm: &'static str,
    file: &'static str,
    /// Whether this theorem is a row of docs/MAP.md's keystone ledger — the
    /// curated public-surface list. This flag is a CLAIM, not a wish: the test
    /// suite parses the ledger, matches each citation by (name, module), and
    /// fails if the flag disagrees in either direction. Unlisted citations
    /// render with an `[unlisted]` marker.
    keystone: bool,
}

/// A citation whose theorem is a row of docs/MAP.md's keystone ledger.
/// (A macro, not a const fn, so the expansion is a struct literal and
/// `&[cite!(…)]` still promotes to `'static` in the table.)
macro_rules! cite {
    ($thm:expr, $file:expr) => {
        Cite { thm: $thm, file: $file, keystone: true }
    };
}

/// The theorem exists in the Lean (existence is test-enforced) but is not on
/// docs/MAP.md's keystone ledger — rendered honestly as `[unlisted]`:
/// classification prose only. When the ledger gains the row, the test suite
/// fails until this is upgraded to `cite!(...)` — growth is conscious in both
/// directions.
macro_rules! cite_unlisted {
    ($thm:expr, $file:expr) => {
        Cite { thm: $thm, file: $file, keystone: false }
    };
}

#[derive(Debug, Clone, Copy)]
struct Exit {
    label: &'static str,
    story: &'static str,
    cites: &'static [Cite],
}

#[derive(Debug, Clone, Copy)]
struct Ruling {
    verdict: Verdict,
    cites: &'static [Cite],
    /// For ESCALATES: the two-replica repro drawn from the Lean witness.
    /// For SEAM / PATTERN: the mechanism and its proved price.
    story: Option<&'static str>,
    /// A caveat worth reading even on a FREE verdict.
    note: Option<&'static str>,
    exits: &'static [Exit],
}

const UNCLASSIFIED_MSG: &str =
    "no theorem in this repo covers this pair; classify it in Lean first";

const DISCLAIMER: &str = "Verdicts are lookups into machine-checked theorems (see Uwueave/), not a \
     checker running here. The counterexamples are real states you can replay in tests.";

// The Lean files cited below (paths relative to the repo root).
const CONFLUENCE: &str = "Uwueave/Confluence.lean";
const CATALOG: &str = "Uwueave/Catalog.lean";
const ACYCLICITY: &str = "Uwueave/Acyclicity.lean";
const MOVE: &str = "Uwueave/Move.lean";
const ORSET_L: &str = "Uwueave/ORSet.lean";
const MVREGISTER: &str = "Uwueave/MVRegister.lean";
const SEGMENTED: &str = "Uwueave/Segmented.lean";
const CAUSALITY: &str = "Uwueave/Causality.lean";
const WEAVE: &str = "Uwueave/Weave.lean";

/// Every ESCALATES verdict is constructive — this is the theorem that turns a
/// failed invariant into a runnable two-replica repro.
const ESCALATION_WITNESS: Cite = cite!("escalation_witness", CONFLUENCE);

// ---------------------------------------------------------------------------
// Shared exit descriptions (each cites the theorem that blesses it)
// ---------------------------------------------------------------------------

// thm: escrow_local_bound_iconfluent, escrow_global_bound
const EXIT_ESCROW: Exit = Exit {
    label: "escrow",
    story: "pre-partition the bound into per-replica quotas. Each replica's local \
            bound survives every merge, and the global bound follows by summing \
            the quotas.",
    cites: &[
        cite!("escrow_local_bound_iconfluent", CATALOG),
        cite_unlisted!("escrow_global_bound", CATALOG),
    ],
};

// thm: budget_segmented
const EXIT_SEAM: Exit = Exit {
    label: "segmented (re-allocation seam)",
    story: "run free within an allocation and coordinate only to change the \
            allocation — one invariant, both verdicts, with the seam named.",
    cites: &[cite!("budget_segmented", SEGMENTED)],
};

// thm: derived_view_sec (price: view_not_stable)
const EXIT_OPLOG: Exit = Exit {
    label: "op-log",
    story: "replicate the operations (a grow-only set, trivially free) and derive \
            the structure by deterministic replay that skips invariant-violating \
            ops. The honest price, also a theorem (view_not_stable): an older \
            remote op can retroactively un-apply an edit you watched happen.",
    cites: &[
        cite!("derived_view_sec", MOVE),
        cite!("view_not_stable", MOVE),
    ],
};

// thm: conflict_surfaces, resolution_is_a_write
const EXIT_MV: Exit = Exit {
    label: "multi-value register",
    story: "keep every non-superseded write and surface concurrent writes as a \
            visible conflict; resolving it is an ordinary write at a dominating \
            clock.",
    cites: &[
        cite!("conflict_surfaces", MVREGISTER),
        cite!("resolution_is_a_write", MVREGISTER),
    ],
};

// thm: lww_every_invariant_iconfluent
const EXIT_LWW: Exit = Exit {
    label: "LWW arbitration",
    story: "hold the value in a single last-writer-wins register: the join selects \
            one write, so no invariant on that one register can break — someone \
            loses, silently, and that is the trade.",
    cites: &[cite!("lww_every_invariant_iconfluent", CATALOG)],
};

// thm: per_user_activation_free, pi_iconfluent
const EXIT_PER_USER: Exit = Exit {
    label: "per-user",
    story: "scope the state per user (a keyed map): each user owns their own copy, \
            and whatever per-user invariant you keep lifts pointwise to the whole \
            map.",
    cites: &[
        cite_unlisted!("per_user_activation_free", WEAVE),
        cite!("pi_iconfluent", CONFLUENCE),
    ],
};

// thm: causal_dag_free (the packaged keystone) = grounded_iconfluent +
// grounded_acyclic (the pair it conjoins, keystones themselves)
const EXIT_GROUNDED: Exit = Exit {
    label: "content-addressed insertion (causal-dag)",
    story: "fix parents at creation and derive ids from content: every edge \
            descends in rank, which is free and implies acyclicity — no cycle \
            check at any replication scale.",
    cites: &[
        cite!("causal_dag_free", ACYCLICITY),
        cite!("grounded_iconfluent", ACYCLICITY),
        cite!("grounded_acyclic", ACYCLICITY),
    ],
};

// thm: orset_present_survives
const EXIT_ORSET_SCOPED: Exit = Exit {
    label: "scoped add-wins guarantee",
    story: "state the feature in the form that is actually true: presence through \
            a tag the other side has not tombstoned survives the merge. That \
            conditional is what \"add-wins\" means.",
    cites: &[cite!("orset_present_survives", ORSET_L)],
};

// thm: clset_present_iconfluent
const EXIT_CLSET: Exit = Exit {
    label: "causal-length set",
    story: "presence as counter parity is free per element; the arbitration is \
            baked in — a longer remote history wins the element.",
    cites: &[cite!("clset_present_iconfluent", ORSET_L)],
};

// thm: fork_evidence_iconfluent, no_unilateral_evidence
const EXIT_DETECT: Exit = Exit {
    label: "accountable detection",
    story: "prevention needs coordination, but detection is free: two signed \
            blocks at one slot are themselves the proof, the evidence survives \
            every future merge, and a replica holding one block frames nobody.",
    cites: &[
        cite!("fork_evidence_iconfluent", CAUSALITY),
        cite_unlisted!("no_unilateral_evidence", CAUSALITY),
    ],
};

// ---------------------------------------------------------------------------
// Shared stories and notes
// ---------------------------------------------------------------------------

const SEAM_STORY: &str =
    "Globally the invariant fails: two different legal allocations of a budget of \
     10 (10+0 and 0+10) merge by pointwise max to 10+10 — over budget \
     (budget_not_iconfluent). Within one allocation it is free: same-allocation \
     replicas merge safely and stay in their segment (budget_segmented). Spends \
     never wait; only re-allocation coordinates.";

const LWW_SINGLE_NOTE: &str =
    "the join selects one of the two writes (LWW.join_selects), so no invariant \
     reading this single register can break at merge — but the losing write \
     vanishes without a trace, and any invariant relating this field to another \
     is the cross-field row instead.";

// The seven single-register kinds share one universally-quantified theorem.
// thm: lww_every_invariant_iconfluent (via selection: LWW.join_selects)
const LWW_SINGLE: Ruling = Ruling {
    verdict: Verdict::Free,
    cites: &[
        cite!("lww_every_invariant_iconfluent", CATALOG),
        cite_unlisted!("LWW.join_selects", CATALOG),
    ],
    story: None,
    note: Some(LWW_SINGLE_NOTE),
    exits: &[],
};

// thm: escrow_local_bound_iconfluent + budget_segmented (+ budget_not_iconfluent)
const QUOTA_SEAM: Ruling = Ruling {
    verdict: Verdict::Seam,
    cites: &[
        cite!("escrow_local_bound_iconfluent", CATALOG),
        cite!("budget_segmented", SEGMENTED),
        cite!("budget_not_iconfluent", SEGMENTED),
    ],
    story: Some(SEAM_STORY),
    note: None,
    exits: &[],
};

// thm: active_path_not_iconfluent
const ACTIVE_PATH_ESCALATES: Ruling = Ruling {
    verdict: Verdict::Escalates,
    cites: &[cite!("active_path_not_iconfluent", WEAVE)],
    story: Some(
        "Replica A activates branch 1 — a legal root-to-leaf path. Replica B \
         activates the sibling branch 2 — also legal. The merged flag-set lights \
         both branches, which is no longer a path: \"the document's one active \
         path\" cannot be shared replicated state.",
    ),
    note: None,
    exits: &[EXIT_PER_USER, EXIT_LWW],
};

// thm: pncounter_nonneg_not_iconfluent
const PN_BALANCE_STORY: &str =
    "Both replicas start from the same 10 credited. Each spends 10 against its \
     own decrement key — individually legal, net exactly 0. The merged counter \
     has spent 20 against 10: net −10. A bounded shared resource cannot be \
     replicated coordination-free.";

// ============================================================================
// THE VERDICT TABLE — one arm per (shape, kind) pair the Lean settles.
// Each entry's comment names its theorem. Everything else is UNCLASSIFIED.
// ============================================================================

fn classify(shape: Shape, kind: Kind) -> Option<Ruling> {
    use Kind::*;
    use Shape::*;
    match (shape, kind) {
        // ------------------------------------------------------------- gset
        // thm: gset_mem_iconfluent
        (GSet, Member) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite!("gset_mem_iconfluent", CATALOG)],
            story: None,
            note: Some(
                "anything a replica has observed survives every merge — the tier-1 \
                 workhorse behind presence, tombstones, bookmarks and acks.",
            ),
            exits: &[],
        }),
        // thm: gset_notmem_iconfluent
        (GSet, NotMember) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite_unlisted!("gset_notmem_iconfluent", CATALOG)],
            story: None,
            note: Some(
                "a union of two sets both lacking the element lacks it; together \
                 with the member row this is why 2P-set presence is confluent — \
                 the 2P price (no re-add) is paid elsewhere, not at merge.",
            ),
            exits: &[],
        }),
        // thm: gset_monotone_iconfluent
        (GSet, LowerBound) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite!("gset_monotone_iconfluent", CATALOG)],
            story: None,
            note: Some(
                "\"at least these members\" is upward-closed under inclusion — the \
                 general positive form: every monotone-closed invariant survives \
                 union.",
            ),
            exits: &[],
        }),
        // thm: gset_atMostOne_not_iconfluent
        (GSet, Ceiling) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[cite!("gset_atMostOne_not_iconfluent", CATALOG)],
            story: Some(
                "Replica A's set is {0}; replica B's is {1} — each within a cap of \
                 one. The merge is union: {0, 1}, and the ceiling breaks. Any cap \
                 on a grow-only structure escalates this way — a union is never \
                 smaller than either side.",
            ),
            note: None,
            exits: &[EXIT_ESCROW, EXIT_SEAM, EXIT_OPLOG],
        }),
        // thm: gset_atMostOne_not_iconfluent
        (GSet, Unique) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[cite!("gset_atMostOne_not_iconfluent", CATALOG)],
            story: Some(
                "Replica A pins item 0; replica B pins item 1. Each replica holds \
                 exactly one pin — perfectly legal. The merge is union, so it holds \
                 both pins, and \"at most one\" is dead; no cleverer merge exists, \
                 because union is what a grow-only set means.",
            ),
            note: None,
            exits: &[EXIT_LWW, EXIT_MV, EXIT_OPLOG],
        }),
        // thm: or_breaks_iconfluence
        (GSet, Mutex) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[cite!("or_breaks_iconfluence", CATALOG)],
            story: Some(
                "Replica A watches Alice take the lock: her flag set, Bob's clear. \
                 Replica B watches Bob take it. Both states satisfy \"exactly one \
                 holder\", and the merged set raises both flags — two holders of a \
                 mutual exclusion. However you phrase a lock, the disjunction shape \
                 cannot be replicated coordination-free.",
            ),
            note: None,
            exits: &[EXIT_LWW, EXIT_MV],
        }),
        // thm: escrow_local_bound_iconfluent + budget_segmented
        (GSet, PerReplicaQuota) => Some(Ruling {
            note: Some(
                "for a set, track per-device add-counts as the escrowed counter — \
                 this is Weave.lean's classification of bookmark caps: per-device \
                 caps are free, a shared global cap is the ceiling row.",
            ),
            ..QUOTA_SEAM
        }),
        // thm: acyclicity_not_iconfluent
        (GSet, Acyclic) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[cite!("acyclicity_not_iconfluent", ACYCLICITY)],
            story: Some(
                "Replica A inserts the edge 0 → 1; replica B inserts 1 → 0. Each \
                 graph is a DAG on its own; the union contains the 2-cycle. By \
                 Bailis necessity no library can offer coordination-free arbitrary \
                 edge insertion with a DAG guarantee — a design that claims to is \
                 hiding coordination or a repair policy.",
            ),
            note: None,
            exits: &[EXIT_GROUNDED, EXIT_OPLOG],
        }),
        // thm: active_path_not_iconfluent
        (GSet, ActivePath) => Some(ACTIVE_PATH_ESCALATES),

        // --------------------------------------------------------- gcounter
        // thm: gcounter_lowerBound_iconfluent
        (GCounter, LowerBound) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite_unlisted!("gcounter_lowerBound_iconfluent", CATALOG)],
            story: None,
            note: Some("merge only raises counts, so a grow-only floor survives."),
            exits: &[],
        }),
        // thm: escrow_local_bound_iconfluent (the escrow carrier IS a G-Counter)
        (GCounter, Ceiling) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite!("escrow_local_bound_iconfluent", CATALOG)],
            story: None,
            note: Some(
                "the proved bound is per-key (f i ≤ q i — the escrow carrier is \
                 exactly a G-Counter merged by max). A cap on the cross-replica \
                 total is not this row; see per-replica-quota for the seam story.",
            ),
            exits: &[],
        }),
        // thm: budget_segmented (+ escrow_local_bound_iconfluent)
        (GCounter, PerReplicaQuota) => Some(QUOTA_SEAM),

        // -------------------------------------------------------- pncounter
        // thm: pncounter_nonneg_not_iconfluent
        (PnCounter, Balance) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[cite!("pncounter_nonneg_not_iconfluent", CATALOG)],
            story: Some(PN_BALANCE_STORY),
            note: None,
            exits: &[EXIT_ESCROW, EXIT_SEAM],
        }),
        // thm: pncounter_nonneg_not_iconfluent (the proved instance is 0 ≤ net)
        (PnCounter, LowerBound) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[cite!("pncounter_nonneg_not_iconfluent", CATALOG)],
            story: Some(PN_BALANCE_STORY),
            note: Some(
                "the proved instance is 0 ≤ net — a balance IS a lower bound on the \
                 net. A floor on a single grow-only component is the gcounter row, \
                 and that one is free.",
            ),
            exits: &[EXIT_ESCROW, EXIT_SEAM],
        }),

        // -------------------------------------------------------------- lww
        // thm: lww_every_invariant_iconfluent — one quantified theorem covers
        // every invariant that reads this single register.
        (Lww, Member | NotMember | LowerBound | Ceiling | Unique | Mutex | Balance) => {
            Some(LWW_SINGLE)
        }
        // thm: lww_cross_field_not_iconfluent
        (Lww, CrossField) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[cite!("lww_cross_field_not_iconfluent", CATALOG)],
            story: Some(
                "The invariant relates two registers: fieldA ≤ fieldB. Replica A \
                 writes both fields to 5 at t=2; replica B writes fieldA := 0 at \
                 t=1 (stale — loses) and fieldB := 0 at t=3 (fresh — wins). The \
                 merge keeps A's fieldA and B's fieldB: (5, 0), an interleaving \
                 neither replica ever held, and the invariant dies.",
            ),
            note: None,
            exits: &[EXIT_MV, EXIT_OPLOG],
        }),
        // thm: per_user_activation_free
        (Lww, ActivePath) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[
                cite_unlisted!("per_user_activation_free", WEAVE),
                cite!("pi_iconfluent", CONFLUENCE),
            ],
            story: None,
            note: Some(
                "per-user activation as a keyed register map: each user owns their \
                 own path, and per-user invariants lift pointwise. The shared \
                 single active path is the gset row, and it escalates.",
            ),
            exits: &[],
        }),

        // ------------------------------------------------------------ mvreg
        // thm: gset_mem_iconfluent (the MV state is a grow-only set of writes)
        (MvReg, Member) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite!("gset_mem_iconfluent", CATALOG)],
            story: None,
            note: Some(
                "the replicated state is a grow-only set of tagged writes, so an \
                 observed write is never lost at merge; what is visible is the \
                 derived view's business.",
            ),
            exits: &[],
        }),
        // thm: conflict_surfaces, view_antichain, resolution_is_a_write
        (MvReg, Unique) => Some(Ruling {
            verdict: Verdict::Pattern,
            cites: &[
                cite!("conflict_surfaces", MVREGISTER),
                cite_unlisted!("view_antichain", MVREGISTER),
                cite!("resolution_is_a_write", MVREGISTER),
            ],
            story: Some(
                "The multi-value register refuses to pick a winner: genuinely \
                 concurrent writes BOTH stay visible after merge \
                 (conflict_surfaces), the visible set is exactly the causal \
                 frontier (view_antichain), and clearing a conflict is just a \
                 write at a dominating clock (resolution_is_a_write). \"At most one \
                 visible value\" is deliberately not a merge invariant here — it is \
                 a UI moment, and for a loom the fork is the product.",
            ),
            note: None,
            exits: &[EXIT_LWW],
        }),

        // ------------------------------------------------------------ orset
        // thm: orset_present_not_iconfluent
        (OrSet, Member) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[cite!("orset_present_not_iconfluent", ORSET_L)],
            story: Some(
                "Both replicas have seen the element added under tags t1 and t2. \
                 Replica A removes what it observed and tombstones t2 — still alive \
                 through t1; replica B symmetrically tombstones t1 — alive through \
                 t2. Each replica shows the element present, but the merge holds \
                 both tombstones, and the element is gone.",
            ),
            note: Some(
                "reachability depends on remove shape (CausalReach): under \
                 tag-scoped rem-after-add the clash is jointly causally Live \
                 (orset_clash_joint); under element-wide rem after both adds it \
                 is unreachable (ew_clashL_unreachable). Operational guarantee \
                 remains the scoped conditional orset_present_survives.",
            ),
            exits: &[EXIT_ORSET_SCOPED, EXIT_CLSET],
        }),

        // ------------------------------------------------------------ clset
        // thm: clset_present_iconfluent
        (ClSet, Member) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite!("clset_present_iconfluent", ORSET_L)],
            story: None,
            note: Some(
                "arbitration is baked in: the replica with the longer causal length \
                 for an element wins it — causal length, not wall-clock recency, is \
                 the tiebreak.",
            ),
            exits: &[],
        }),
        // thm: clset_absent_iconfluent
        (ClSet, NotMember) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite_unlisted!("clset_absent_iconfluent", ORSET_L)],
            story: None,
            note: Some(
                "absence is the same per-key selection argument — the CL-Set has no \
                 analogue of the OR-Set's both-sides-tombstone anomaly.",
            ),
            exits: &[],
        }),
        // thm: clset_cross_element_not_iconfluent
        (ClSet, CrossField) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[cite_unlisted!("clset_cross_element_not_iconfluent", ORSET_L)],
            story: Some(
                "The invariant links elements: if 0 is present then 1 is present. \
                 Replica A holds counts {0 ↦ 3, 1 ↦ 1} — both odd, both present. \
                 Replica B holds {0 ↦ 2, 1 ↦ 2} — 0 even, absent, so the invariant \
                 is vacuous there. Per-key max merges to {0 ↦ 3, 1 ↦ 2}: 0 present, \
                 1 absent — violated. Selection per key is not selection per state.",
            ),
            note: None,
            exits: &[EXIT_MV, EXIT_OPLOG],
        }),

        // ----------------------------------------------------------- escrow
        // thm: gcounter_lowerBound_iconfluent (the escrow carrier is a G-Counter)
        (Escrow, LowerBound) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite_unlisted!("gcounter_lowerBound_iconfluent", CATALOG)],
            story: None,
            note: Some("the escrow carrier is a G-Counter; a grow-only floor survives."),
            exits: &[],
        }),
        // thm: escrow_local_bound_iconfluent (+ escrow_global_bound)
        (Escrow, Ceiling) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[
                cite!("escrow_local_bound_iconfluent", CATALOG),
                cite_unlisted!("escrow_global_bound", CATALOG),
            ],
            story: None,
            note: Some(
                "each replica's spends stay under its own quota through every \
                 merge, and the global cap follows by summing quotas.",
            ),
            exits: &[],
        }),
        // thm: escrow_local_bound_iconfluent (+ escrow_global_bound)
        (Escrow, Balance) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[
                cite!("escrow_local_bound_iconfluent", CATALOG),
                cite_unlisted!("escrow_global_bound", CATALOG),
            ],
            story: None,
            note: Some(
                "the escrow rephrasing of the shared balance: same resource, same \
                 safety goal as the pncounter row, opposite verdict — because the \
                 invariant became per-replica. That rephrasing is the entire escrow \
                 trick.",
            ),
            exits: &[],
        }),
        // thm: budget_segmented (+ budget_not_iconfluent)
        (Escrow, PerReplicaQuota) => Some(QUOTA_SEAM),

        // ------------------------------------------------------- causal-dag
        // thm: gset_mem_iconfluent
        (CausalDag, Member) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite!("gset_mem_iconfluent", CATALOG)],
            story: None,
            note: Some(
                "node presence in an append-only store is G-Set membership; \
                 anything observed survives every merge.",
            ),
            exits: &[],
        }),
        // thm: gset_monotone_iconfluent
        (CausalDag, LowerBound) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite!("gset_monotone_iconfluent", CATALOG)],
            story: None,
            note: Some(
                "\"at least these nodes exist\" is monotone-closed under inclusion, \
                 so it survives union.",
            ),
            exits: &[],
        }),
        // thm: gset_atMostOne_not_iconfluent (exits: Causality.lean's evidence pair)
        (CausalDag, Unique) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[cite!("gset_atMostOne_not_iconfluent", CATALOG)],
            story: Some(
                "An equivocating author signs two different blocks for the same \
                 (author, seq) slot and gossips one to each side of a partition. \
                 Each replica's grow-only store is legal alone; the merge holds \
                 both blocks. Uniqueness-per-slot is a ceiling on a grow-only set — \
                 the proved escalation instance is the {0}/{1} singleton pair.",
            ),
            note: None,
            exits: &[EXIT_DETECT],
        }),
        // thm: causal_dag_free (grounded_iconfluent + grounded_acyclic)
        (CausalDag, Acyclic) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[
                cite!("causal_dag_free", ACYCLICITY),
                cite!("grounded_iconfluent", ACYCLICITY),
                cite!("grounded_acyclic", ACYCLICITY),
            ],
            story: None,
            note: Some(
                "rank comes free from content-addressing (a parent must exist \
                 before its child can be named), so no cycle check runs anywhere. \
                 That a hash cycle is impossible is a collision-resistance premise, \
                 not a Lean theorem — the repo says so out loud.",
            ),
            exits: &[],
        }),
        // thm: active_path_not_iconfluent
        (CausalDag, ActivePath) => Some(ACTIVE_PATH_ESCALATES),

        // ---------------------------------------------------------- movelog
        // thm: gset_mem_iconfluent
        (MoveLog, Member) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[cite!("gset_mem_iconfluent", CATALOG)],
            story: None,
            note: Some(
                "an op, once in the log, survives every merge; whether it still has \
                 an effect is the derived view's business (view_not_stable).",
            ),
            exits: &[],
        }),
        // thm: derived_view_sec + miniInterp_acyclic (price: view_not_stable)
        (MoveLog, Acyclic) => Some(Ruling {
            verdict: Verdict::Pattern,
            cites: &[
                cite!("derived_view_sec", MOVE),
                cite!("miniInterp_acyclic", MOVE),
                cite!("view_not_stable", MOVE),
            ],
            story: Some(
                "Replicate the monotone thing — the grow-only set of move ops — and \
                 derive the tree by timestamp-ordered, cycle-skipping replay; \
                 convergence, redelivery-immunity and the invariant come as one \
                 theorem (derived_view_sec), with enforcement by construction \
                 (miniInterp_acyclic). The proved price is view_not_stable: an op \
                 you watched apply can be retroactively skipped when an older \
                 remote op syncs in — \"my move undid itself\" is the arbitration, \
                 made visible.",
            ),
            note: None,
            exits: &[],
        }),

        // Everything else: the Lean development does not settle it, and this
        // tool never guesses.
        _ => None,
    }
}

// ============================================================================
// Schema parsing
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
struct Schema {
    fields: Vec<(String, Shape)>,
    invariants: Vec<(String, Kind)>,
}

fn parse_schema(text: &str) -> Result<Schema, Vec<String>> {
    let mut fields: Vec<(String, Shape, usize)> = Vec::new();
    let mut invariants: Vec<(String, Kind, usize)> = Vec::new();
    let mut errs: Vec<String> = Vec::new();

    for (idx, raw) in text.lines().enumerate() {
        let no = idx + 1;
        let line = match raw.find('#') {
            Some(i) => &raw[..i],
            None => raw,
        };
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let Some((lhs, rhs)) = line.split_once(':') else {
            errs.push(format!(
                "line {}: expected `field <name>: <shape>` or `invariant <field>: <kind>`, got `{}`",
                no, line
            ));
            continue;
        };
        let rhs = rhs.trim();
        if rhs.split_whitespace().count() != 1 {
            errs.push(format!(
                "line {}: expected exactly one word after the colon, got `{}`",
                no, rhs
            ));
            continue;
        }
        let lhs_tokens: Vec<&str> = lhs.split_whitespace().collect();
        match lhs_tokens.as_slice() {
            ["field", name] => match Shape::parse(rhs) {
                Some(shape) => {
                    if let Some((_, _, prev)) = fields.iter().find(|(n, _, _)| n == name) {
                        errs.push(format!(
                            "line {}: field `{}` was already declared on line {}",
                            no, name, prev
                        ));
                    } else {
                        fields.push(((*name).to_string(), shape, no));
                    }
                }
                None => errs.push(format!(
                    "line {}: unknown shape `{}` — valid shapes: {}",
                    no,
                    rhs,
                    shape_tokens_joined()
                )),
            },
            ["invariant", name] => match Kind::parse(rhs) {
                Some(kind) => invariants.push(((*name).to_string(), kind, no)),
                None => errs.push(format!(
                    "line {}: unknown invariant kind `{}` — valid kinds: {}",
                    no,
                    rhs,
                    kind_tokens_joined()
                )),
            },
            _ => errs.push(format!(
                "line {}: lines start with `field` or `invariant`, got `{}`",
                no, line
            )),
        }
    }

    for (name, _, no) in &invariants {
        if !fields.iter().any(|(n, _, _)| n == name) {
            let declared = if fields.is_empty() {
                "(none)".to_string()
            } else {
                fields
                    .iter()
                    .map(|(n, _, _)| n.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            errs.push(format!(
                "line {}: invariant on undeclared field `{}` — declared fields: {}",
                no, name, declared
            ));
        }
    }

    if errs.is_empty() {
        Ok(Schema {
            fields: fields.into_iter().map(|(n, s, _)| (n, s)).collect(),
            invariants: invariants.into_iter().map(|(n, k, _)| (n, k)).collect(),
        })
    } else {
        Err(errs)
    }
}

// ============================================================================
// Rendering
// ============================================================================

const WRAP_WIDTH: usize = 78;

fn wrap_hanging(text: &str, first_indent: &str, rest_indent: &str) -> String {
    let mut out = String::new();
    let mut line = String::from(first_indent);
    let mut line_has_word = false;
    for word in text.split_whitespace() {
        if line_has_word && line.chars().count() + 1 + word.chars().count() > WRAP_WIDTH {
            out.push_str(&line);
            out.push('\n');
            line = String::from(rest_indent);
            line_has_word = false;
        }
        if line_has_word {
            line.push(' ');
        }
        line.push_str(word);
        line_has_word = true;
    }
    if line_has_word {
        out.push_str(&line);
        out.push('\n');
    }
    out
}

fn wrap(text: &str, indent: &str) -> String {
    wrap_hanging(text, indent, indent)
}

fn cite_string(c: &Cite) -> String {
    if c.keystone {
        format!("{} — {}", c.thm, c.file)
    } else {
        format!("{} [unlisted] — {}", c.thm, c.file)
    }
}

/// Every citation the tool can ever print: rulings, exits, and the
/// escalation-witness coda. The audit tests walk exactly this.
fn all_citations() -> Vec<Cite> {
    let mut cites = vec![ESCALATION_WITNESS];
    for shape in ALL_SHAPES {
        for kind in ALL_KINDS {
            if let Some(ruling) = classify(shape, kind) {
                cites.extend_from_slice(ruling.cites);
                for exit in ruling.exits {
                    cites.extend_from_slice(exit.cites);
                }
            }
        }
    }
    cites
}

/// The distinct citations that stand on theorems the keystone ledger omits.
fn distinct_unlisted() -> Vec<Cite> {
    let mut seen: Vec<Cite> = Vec::new();
    for c in all_citations() {
        if !c.keystone && !seen.contains(&c) {
            seen.push(c);
        }
    }
    seen
}

const LEDGER_FOOTER_CLEAN: &str =
    "Every cited theorem is on docs/MAP.md's keystone ledger (enforced by tests).";

const UNLISTED_LEGEND: &str =
    "[unlisted] — the cited theorem exists in the Lean (existence enforced by \
     tests) but is not on docs/MAP.md's keystone ledger; classification prose \
     only.";

/// One honest line about the ledger cross-check. The tests assert this footer
/// can never claim more than docs/MAP.md actually lists.
fn ledger_footer() -> String {
    let unlisted = distinct_unlisted();
    if unlisted.is_empty() {
        LEDGER_FOOTER_CLEAN.to_string()
    } else {
        format!(
            "Citations are cross-checked against docs/MAP.md's keystone ledger \
             (enforced by tests); {} cited theorem(s) are not on it and are \
             marked [unlisted] — classification prose only.",
            unlisted.len()
        )
    }
}

fn cite_list(cites: &[Cite]) -> String {
    cites.iter().map(cite_string).collect::<Vec<_>>().join("; ")
}

fn render(source: &str, schema: &Schema) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "{} — {} field(s), {} invariant(s)\n\n",
        source,
        schema.fields.len(),
        schema.invariants.len()
    ));

    // Assemble rows.
    struct Row {
        field: String,
        shape: Shape,
        kind: Kind,
        ruling: Option<Ruling>,
    }
    let rows: Vec<Row> = schema
        .invariants
        .iter()
        .map(|(fname, kind)| {
            let shape = schema
                .fields
                .iter()
                .find(|(n, _)| n == fname)
                .map(|(_, s)| *s)
                .expect("parse guarantees every invariant names a declared field");
            Row {
                field: fname.clone(),
                shape,
                kind: *kind,
                ruling: classify(shape, *kind),
            }
        })
        .collect();

    if rows.is_empty() {
        out.push_str("no invariants declared — nothing to classify.\n");
        out.push_str("(declare one with `invariant <field>: <kind>`; see --help)\n");
    } else {
        // The verdict table, aligned, no ANSI.
        let headers = ["FIELD", "SHAPE", "INVARIANT", "VERDICT", "THEOREM(S)"];
        let cells: Vec<[String; 5]> = rows
            .iter()
            .map(|r| {
                let (verdict, thms) = match &r.ruling {
                    Some(ruling) => (ruling.verdict.label().to_string(), cite_list(ruling.cites)),
                    None => (
                        "UNCLASSIFIED".to_string(),
                        format!("— {}", UNCLASSIFIED_MSG),
                    ),
                };
                [
                    r.field.clone(),
                    r.shape.token().to_string(),
                    r.kind.token().to_string(),
                    verdict,
                    thms,
                ]
            })
            .collect();
        let mut widths: [usize; 5] = [0; 5];
        for i in 0..5 {
            widths[i] = headers[i].chars().count();
            for row in &cells {
                widths[i] = widths[i].max(row[i].chars().count());
            }
        }
        let fmt_row = |cols: [&str; 5]| -> String {
            let mut line = String::new();
            for i in 0..5 {
                line.push_str(cols[i]);
                if i < 4 {
                    for _ in cols[i].chars().count()..widths[i] + 2 {
                        line.push(' ');
                    }
                }
            }
            line.push('\n');
            line
        };
        out.push_str(&fmt_row([headers[0], headers[1], headers[2], headers[3], headers[4]]));
        let total: usize = widths.iter().sum::<usize>() + 4 * 2;
        out.push_str(&"-".repeat(total.min(100)));
        out.push('\n');
        for row in &cells {
            out.push_str(&fmt_row([
                &row[0], &row[1], &row[2], &row[3], &row[4],
            ]));
        }

        // If any rendered citation lacks its audit receipt, say what the
        // marker means right here, not in a manual.
        let any_unlisted_rendered = rows.iter().filter_map(|r| r.ruling.as_ref()).any(|ru| {
            ru.cites.iter().any(|c| !c.keystone)
                || ru.exits.iter().any(|e| e.cites.iter().any(|c| !c.keystone))
        });
        if any_unlisted_rendered {
            out.push('\n');
            out.push_str(&wrap(UNLISTED_LEGEND, ""));
        }
    }

    // Fields that carry no invariant at all.
    for (name, shape) in &schema.fields {
        if !schema.invariants.iter().any(|(n, _)| n == name) {
            out.push_str(&format!(
                "\nnote: field `{}` ({}) has no declared invariants — nothing to classify for it.\n",
                name,
                shape.token()
            ));
        }
    }

    // Detail blocks: repro stories, seams, patterns, notes, exits.
    let detailed: Vec<&Row> = rows
        .iter()
        .filter(|r| {
            r.ruling
                .as_ref()
                .map(|ru| ru.story.is_some() || ru.note.is_some() || !ru.exits.is_empty())
                .unwrap_or(false)
        })
        .collect();
    if !detailed.is_empty() {
        out.push_str("\ndetails\n=======\n");
        for r in &detailed {
            let ruling = r.ruling.as_ref().unwrap();
            out.push_str(&format!(
                "\n{} · {} — {}\n",
                r.field,
                r.kind.token(),
                ruling.verdict.label()
            ));
            out.push_str(&wrap(&format!("cites: {}", cite_list(ruling.cites)), "  "));
            if let Some(story) = ruling.story {
                let header = match ruling.verdict {
                    Verdict::Escalates => "the two-replica repro:",
                    Verdict::Seam => "the seam:",
                    Verdict::Pattern => "the pattern:",
                    Verdict::Free => "the story:",
                };
                out.push_str(&format!("  {}\n", header));
                out.push_str(&wrap(story, "    "));
            }
            if !ruling.exits.is_empty() {
                out.push_str("  ways out:\n");
                for exit in ruling.exits {
                    out.push_str(&wrap_hanging(
                        &format!("- {}: {}", exit.label, exit.story),
                        "    ",
                        "      ",
                    ));
                    out.push_str(&wrap(&format!("({})", cite_list(exit.cites)), "      "));
                }
            }
            if let Some(note) = ruling.note {
                out.push_str(&wrap(&format!("note: {}", note), "  "));
            }
        }
        if detailed
            .iter()
            .any(|r| r.ruling.as_ref().unwrap().verdict == Verdict::Escalates)
        {
            out.push('\n');
            out.push_str(&wrap(
                &format!(
                    "Every ESCALATES verdict is constructive: a failed invariant always \
                     yields a runnable two-replica repro ({}).",
                    cite_string(&ESCALATION_WITNESS)
                ),
                "",
            ));
        }
    }

    out.push('\n');
    out.push_str(&"-".repeat(WRAP_WIDTH));
    out.push('\n');
    out.push_str(&wrap(DISCLAIMER, ""));
    out.push_str(&wrap(&ledger_footer(), ""));
    out
}

// ============================================================================
// Help
// ============================================================================

fn help_text() -> String {
    let mut h = String::new();
    let p = |h: &mut String, s: &str| {
        h.push_str(s);
        h.push('\n');
    };
    p(&mut h, "uwueave-check — is your invariant safe to replicate?");
    p(&mut h, "");
    p(&mut h, "USAGE");
    p(&mut h, "  uwueave-check <schema-file>");
    p(&mut h, "  uwueave-check --help");
    p(&mut h, "");
    p(&mut h, "Describe your replicated fields and the invariants you care about; this tool");
    p(&mut h, "answers, per invariant, whether the merge can break it — by looking the pair");
    p(&mut h, "up in this repo's catalog of machine-checked theorems and citing the exact");
    p(&mut h, "theorem that settles it. Where no theorem covers a pair, it says so plainly");
    p(&mut h, "instead of guessing.");
    p(&mut h, "");
    p(&mut h, "SCHEMA FORMAT (line-based; `#` starts a comment, blank lines are fine)");
    p(&mut h, "");
    p(&mut h, "  field <name>: <shape>         declare a replicated field");
    p(&mut h, "  invariant <field>: <kind>     ask about an invariant on that field");
    p(&mut h, "");
    p(&mut h, "  Declarations may come in any order; one field may carry several invariants.");
    p(&mut h, "");
    p(&mut h, "SHAPES");
    p(&mut h, "  gset         grow-only set (merge = union)");
    p(&mut h, "  gcounter     per-replica grow-only counter (merge = pointwise max)");
    p(&mut h, "  pncounter    increments and decrements; the observable is the net");
    p(&mut h, "  lww          last-writer-wins register (timestamped; the join selects)");
    p(&mut h, "  mvreg        multi-value register (concurrent writes stay visible)");
    p(&mut h, "  orset        observed-remove set (add-wins via tags)");
    p(&mut h, "  clset        causal-length set (presence = counter parity)");
    p(&mut h, "  escrow       per-replica quota'd spends (the escrowed bounded counter)");
    p(&mut h, "  causal-dag   content-addressed append-only DAG (parents fixed at creation)");
    p(&mut h, "  movelog      grow-only op log; structure derived by cycle-skipping replay");
    p(&mut h, "");
    p(&mut h, "INVARIANT KINDS");
    p(&mut h, "  member             this element/value stays present");
    p(&mut h, "  not-member         this element stays absent");
    p(&mut h, "  lower-bound        at least k (a grow-only floor)");
    p(&mut h, "  ceiling            at most k (a cap on size or value)");
    p(&mut h, "  unique             at most one — one pin, one entry per key");
    p(&mut h, "  mutex              exactly one of several parties holds it");
    p(&mut h, "  balance            a resource never goes negative");
    p(&mut h, "  per-replica-quota  each replica stays within its own allocation");
    p(&mut h, "  acyclic            the graph/tree stays cycle-free");
    p(&mut h, "  active-path        one shared active root-to-leaf path");
    p(&mut h, "  cross-field        an invariant relating two fields or elements");
    p(&mut h, "");
    p(&mut h, "VERDICTS");
    p(&mut h, "  FREE           the merge provably cannot break it; the theorem is cited");
    p(&mut h, "  ESCALATES      two legal replicas can merge into an illegal state — the");
    p(&mut h, "                 exact pair is in the theorem, retold in the report, along");
    p(&mut h, "                 with suggested exits (escrow / op-log / MV / per-user)");
    p(&mut h, "  SEAM           free within an allocation; coordination only at the seam");
    p(&mut h, "                 (re-allocation) — the segmented-confluence verdict");
    p(&mut h, "  PATTERN        maintained by the op-log / derived-view pattern, with a");
    p(&mut h, "                 proved price (an older remote op can rewrite what you saw)");
    p(&mut h, "  UNCLASSIFIED   no theorem in this repo covers this pair; classify it in");
    p(&mut h, "                 Lean first — this tool never guesses");
    p(&mut h, "");
    p(&mut h, "EXAMPLE (save as loom.schema, then run `uwueave-check loom.schema`)");
    p(&mut h, "");
    p(&mut h, "  # a tiny loom, field by field");
    p(&mut h, "  field nodes: causal-dag       # hash-linked, parents fixed at creation");
    p(&mut h, "  field bookmarks: gset");
    p(&mut h, "  field wallet: pncounter");
    p(&mut h, "  field title: lww");
    p(&mut h, "  field moves: movelog");
    p(&mut h, "");
    p(&mut h, "  invariant nodes: acyclic      # FREE — causal_dag_free");
    p(&mut h, "  invariant bookmarks: member   # FREE — gset_mem_iconfluent");
    p(&mut h, "  invariant bookmarks: ceiling  # ESCALATES — with escrow/seam exits");
    p(&mut h, "  invariant wallet: balance     # ESCALATES — Bailis's bank account");
    p(&mut h, "  invariant title: cross-field  # ESCALATES — the LWW interleaving");
    p(&mut h, "  invariant moves: acyclic      # PATTERN — derived view, priced honestly");
    p(&mut h, "");
    h.push_str(&wrap(DISCLAIMER, ""));
    h.push_str(&wrap(&ledger_footer(), ""));
    h
}

// ============================================================================
// main
// ============================================================================

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.iter().any(|a| a == "-h" || a == "--help") {
        print!("{}", help_text());
        return;
    }
    let path = match args.len() {
        1 => &args[0],
        0 => {
            eprint!("{}", help_text());
            process::exit(2);
        }
        _ => {
            eprintln!(
                "uwueave-check: expected exactly one schema file, got {} arguments; try --help",
                args.len()
            );
            process::exit(2);
        }
    };
    let text = match fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("uwueave-check: could not read `{}`: {}", path, e);
            process::exit(1);
        }
    };
    match parse_schema(&text) {
        Ok(schema) => print!("{}", render(path, &schema)),
        Err(errs) => {
            for e in &errs {
                eprintln!("uwueave-check: {}: {}", path, e);
            }
            eprintln!(
                "uwueave-check: {} error(s); nothing classified. try --help for the format.",
                errs.len()
            );
            process::exit(1);
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    impl Schema {
        fn to_text(&self) -> String {
            let mut s = String::new();
            for (n, shape) in &self.fields {
                s.push_str(&format!("field {}: {}\n", n, shape.token()));
            }
            for (n, kind) in &self.invariants {
                s.push_str(&format!("invariant {}: {}\n", n, kind.token()));
            }
            s
        }
    }

    const SAMPLE: &str = "# demo schema\n\
                          field notes: gset\n\
                          field wallet: pncounter   # trailing comment\n\
                          \n\
                          invariant notes: member\n\
                          invariant wallet: balance\n";

    #[test]
    fn parse_round_trips() {
        let schema = parse_schema(SAMPLE).expect("sample parses");
        assert_eq!(
            schema.fields,
            vec![
                ("notes".to_string(), Shape::GSet),
                ("wallet".to_string(), Shape::PnCounter),
            ]
        );
        assert_eq!(
            schema.invariants,
            vec![
                ("notes".to_string(), Kind::Member),
                ("wallet".to_string(), Kind::Balance),
            ]
        );
        // text -> Schema -> text -> Schema is a fixed point.
        let reparsed = parse_schema(&schema.to_text()).expect("rendered schema parses");
        assert_eq!(schema, reparsed);
        // every shape and kind token survives its own round trip
        for shape in ALL_SHAPES {
            assert_eq!(Shape::parse(shape.token()), Some(shape));
        }
        for kind in ALL_KINDS {
            assert_eq!(Kind::parse(kind.token()), Some(kind));
        }
    }

    #[test]
    fn known_free_lookup() {
        let ruling = classify(Shape::GSet, Kind::Member).expect("gset/member is classified");
        assert_eq!(ruling.verdict, Verdict::Free);
        // No [unlisted] marker: gset_mem_iconfluent is a keystone-ledger row
        // in docs/MAP.md. If it ever leaves the ledger, the resolve test forces
        // the citation to cite_unlisted!(...) — update this expectation with it.
        assert_eq!(
            cite_string(&ruling.cites[0]),
            "gset_mem_iconfluent — Uwueave/Catalog.lean"
        );
    }

    #[test]
    fn known_escalates_lookup_with_citation() {
        let ruling = classify(Shape::GSet, Kind::Unique).expect("gset/unique is classified");
        assert_eq!(ruling.verdict, Verdict::Escalates);
        assert_eq!(
            cite_string(&ruling.cites[0]),
            "gset_atMostOne_not_iconfluent — Uwueave/Catalog.lean"
        );
        // The repro retells the Lean witness: the {0}/{1} pins merging to two pins.
        let story = ruling.story.expect("escalation carries its repro");
        assert!(story.contains("pins item 0"));
        assert!(story.contains("pins item 1"));
        assert!(!ruling.exits.is_empty(), "escalation suggests exits");
    }

    #[test]
    fn unclassified_pair_is_honest() {
        assert!(classify(Shape::PnCounter, Kind::Ceiling).is_none());
        assert!(classify(Shape::OrSet, Kind::Acyclic).is_none());
        // This token pair cannot honestly inherit the bookmark theorem. Lean
        // settles one relation over two GSets as FREE
        // (`Spec.pointsAtExisting_iconfluent`) and another as a clash
        // (`Spec.censusClash`). The schema language does not name which
        // relation was meant, so choosing either verdict here would invent
        // semantics that are absent from the input.
        assert!(classify(Shape::GSet, Kind::CrossField).is_none());
        // ... and the rendered report says the exact honest sentence.
        let schema = parse_schema("field w: pncounter\ninvariant w: ceiling\n").unwrap();
        let report = render("test.schema", &schema);
        assert!(report.contains("UNCLASSIFIED"));
        assert!(report.contains(UNCLASSIFIED_MSG));
    }

    #[test]
    fn unknown_shape_error_lists_options() {
        let errs = parse_schema("field x: gsett\n").unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].contains("unknown shape `gsett`"));
        assert!(errs[0].contains("valid shapes"));
        assert!(errs[0].contains("causal-dag"), "options are listed: {}", errs[0]);
    }

    #[test]
    fn unknown_kind_error_lists_options() {
        let errs = parse_schema("field x: gset\ninvariant x: uniq\n").unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].contains("unknown invariant kind `uniq`"));
        assert!(errs[0].contains("per-replica-quota"), "options listed: {}", errs[0]);
    }

    #[test]
    fn malformed_lines_and_unknown_fields_error() {
        let errs =
            parse_schema("field x gset\ninvariant y: member\nfield x: gset\nfield x: gset\n")
                .unwrap_err();
        assert!(errs.iter().any(|e| e.starts_with("line 1:")), "{:?}", errs);
        assert!(
            errs.iter().any(|e| e.contains("undeclared field `y`")),
            "{:?}",
            errs
        );
        assert!(
            errs.iter().any(|e| e.contains("already declared")),
            "{:?}",
            errs
        );
    }

    #[test]
    fn every_escalation_has_repro_and_exits() {
        for shape in ALL_SHAPES {
            for kind in ALL_KINDS {
                if let Some(ruling) = classify(shape, kind) {
                    if ruling.verdict == Verdict::Escalates {
                        assert!(
                            ruling.story.is_some(),
                            "({}, {}) escalates without a repro story",
                            shape.token(),
                            kind.token()
                        );
                        assert!(
                            !ruling.exits.is_empty(),
                            "({}, {}) escalates without suggested exits",
                            shape.token(),
                            kind.token()
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn coverage_counts_are_pinned() {
        let mut classified = 0;
        let mut unclassified = 0;
        for shape in ALL_SHAPES {
            for kind in ALL_KINDS {
                match classify(shape, kind) {
                    Some(_) => classified += 1,
                    None => unclassified += 1,
                }
            }
        }
        assert_eq!(classified + unclassified, 110);
        // A deliberate pin: growing the Lean catalog should consciously bump this.
        assert_eq!(classified, 40);
    }

    // ========================================================================
    // The audit gate — the mechanism that makes catalog↔Lean disagreement a
    // test failure instead of a drift. All scans run over comment-STRIPPED
    // Lean source, so prose can neither satisfy nor confuse a check.
    // ========================================================================

    /// Walk up from CARGO_MANIFEST_DIR (rust/) to the repo root — the
    /// directory that contains Uwueave/.
    fn repo_root() -> std::path::PathBuf {
        let mut root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        loop {
            if root.join("Uwueave").is_dir() {
                return root;
            }
            assert!(
                root.pop(),
                "no directory containing Uwueave/ above CARGO_MANIFEST_DIR"
            );
        }
    }

    /// Blank out Lean comments (`-- …` and nested `/- … -/`), preserving
    /// newlines and all code characters, so later scans cannot match inside
    /// docstrings or prose.
    fn strip_lean_comments(src: &str) -> String {
        let chars: Vec<char> = src.chars().collect();
        let mut out = String::with_capacity(src.len());
        let mut i = 0;
        let mut depth = 0usize;
        let mut line_comment = false;
        while i < chars.len() {
            let c = chars[i];
            let next = chars.get(i + 1).copied();
            if line_comment {
                if c == '\n' {
                    line_comment = false;
                    out.push('\n');
                } else {
                    out.push(' ');
                }
                i += 1;
            } else if depth > 0 {
                if c == '-' && next == Some('/') {
                    depth -= 1;
                    out.push_str("  ");
                    i += 2;
                } else if c == '/' && next == Some('-') {
                    depth += 1;
                    out.push_str("  ");
                    i += 2;
                } else {
                    out.push(if c == '\n' { '\n' } else { ' ' });
                    i += 1;
                }
            } else if c == '/' && next == Some('-') {
                depth = 1;
                out.push_str("  ");
                i += 2;
            } else if c == '-' && next == Some('-') {
                line_comment = true;
                out.push_str("  ");
                i += 2;
            } else {
                out.push(c);
                i += 1;
            }
        }
        out
    }

    /// The rows of docs/MAP.md's `## Keystone ledger` table, as
    /// (theorem-name-as-cited, module) pairs — the curated public-surface
    /// list the CLI may claim. Keyed by name AND module because display
    /// names collide (`wf_iconfluent` is both a Sequence and an Authority
    /// row); a name alone is not a key.
    fn keystone_ledger(root: &std::path::Path) -> Vec<(String, String)> {
        let path = root.join("docs/MAP.md");
        let content = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("could not read {}: {}", path.display(), e));
        let heading = content.find("## Keystone ledger").unwrap_or_else(|| {
            panic!(
                "docs/MAP.md no longer has a `## Keystone ledger` section — \
                 re-point the CLI's citation gate consciously"
            )
        });
        let section = &content[heading..];
        let section = match section[2..].find("\n## ") {
            Some(i) => &section[..i + 2],
            None => section,
        };
        let mut rows = Vec::new();
        for line in section.lines() {
            let cells: Vec<&str> = line.split('|').map(str::trim).collect();
            // A ledger row is `| `name` … | Module | … |`.
            if cells.len() < 3 {
                continue;
            }
            let (first, module) = (cells[1], cells[2]);
            let Some(rest) = first.strip_prefix('`') else {
                continue; // header or separator row
            };
            let Some(tick) = rest.find('`') else { continue };
            let name = &rest[..tick];
            assert!(
                !name.is_empty() && !module.is_empty() && !module.contains('`'),
                "unparseable keystone-ledger row in docs/MAP.md: `{}`",
                line
            );
            rows.push((name.to_string(), module.to_string()));
        }
        // If this parser goes half-blind the gate must go red, not silently
        // green: the section's own "N rows:" summary must agree when present.
        if let Some(idx) = section.find(" rows:") {
            let digits: String = section[..idx]
                .chars()
                .rev()
                .take_while(|c| c.is_ascii_digit())
                .collect();
            let stated: usize = digits
                .chars()
                .rev()
                .collect::<String>()
                .parse()
                .expect("digits before ' rows:'");
            assert_eq!(
                rows.len(),
                stated,
                "parsed {} keystone-ledger rows but docs/MAP.md says {} — the \
                 table and its summary (or this parser) disagree",
                rows.len(),
                stated
            );
        }
        assert!(
            rows.len() >= 50,
            "only {} keystone-ledger rows parsed from docs/MAP.md — the table \
             format moved or the ledger shrank; update this parser consciously",
            rows.len()
        );
        assert!(
            rows.iter()
                .any(|(n, m)| n == "escalation_witness" && m == "Confluence"),
            "docs/MAP.md's ledger no longer lists escalation_witness — parser \
             or ledger regressed"
        );
        rows
    }

    /// Byte offset (in comment-stripped text) of `theorem <name>` as a whole
    /// word, or None.
    fn find_theorem_def(stripped: &str, name: &str) -> Option<usize> {
        let needle = format!("theorem {}", name);
        let mut start = 0;
        while let Some(pos) = stripped[start..].find(&needle) {
            let abs = start + pos;
            let after = abs + needle.len();
            let after_ok = match stripped[after..].chars().next() {
                None => true,
                Some(c) => !(c.is_ascii_alphanumeric() || c == '_' || c == '\''),
            };
            let before_ok = stripped[..abs]
                .chars()
                .last()
                .map_or(true, |c| !(c.is_ascii_alphanumeric() || c == '_'));
            if after_ok && before_ok {
                return Some(abs);
            }
            start = after;
        }
        None
    }

    /// The namespace prefix in force at `offset`, tracked through
    /// namespace/section opens and their matching `end`s. Panics — a test
    /// failure, not a guess — on any scope shape it cannot account for.
    fn namespace_stack_at(stripped: &str, offset: usize, file: &str) -> Vec<String> {
        #[derive(PartialEq)]
        enum Kind {
            Namespace,
            Section,
        }
        let mut stack: Vec<(Kind, String)> = Vec::new();
        let mut pos = 0;
        for line in stripped.split_inclusive('\n') {
            let line_start = pos;
            pos += line.len();
            if line_start >= offset {
                break;
            }
            let t = line.trim();
            if let Some(rest) = t.strip_prefix("namespace ") {
                let name = rest.split_whitespace().next().unwrap_or("").to_string();
                assert!(!name.is_empty(), "{}: nameless `namespace`", file);
                stack.push((Kind::Namespace, name));
            } else if t == "section" {
                stack.push((Kind::Section, String::new()));
            } else if let Some(rest) = t.strip_prefix("section ") {
                let name = rest.split_whitespace().next().unwrap_or("").to_string();
                stack.push((Kind::Section, name));
            } else if t == "end" || t.starts_with("end ") {
                let name = t.strip_prefix("end").unwrap().trim();
                let (_, top) = stack
                    .pop()
                    .unwrap_or_else(|| panic!("{}: `{}` with no open scope", file, t));
                assert!(
                    top == name,
                    "{}: `end {}` closed a scope opened as `{}` — this scanner \
                     needs a conscious upgrade for that shape",
                    file,
                    name,
                    top
                );
            }
        }
        stack
            .into_iter()
            .filter(|(k, _)| *k == Kind::Namespace)
            .map(|(_, n)| n)
            .collect()
    }

    /// Resolve a citation to (fully-qualified Lean name, definition offset)
    /// using the cited file's actual namespace structure. A display name is
    /// not a key: the citation's spelling must be a dot-suffix of the real
    /// name, and pin membership is decided on the full name only.
    fn resolve_citation(stripped: &str, cite: &Cite) -> (String, usize) {
        let bare = cite.thm.rsplit('.').next().unwrap();
        let (as_written, off) = match find_theorem_def(stripped, cite.thm) {
            Some(off) => (cite.thm, off),
            None => (
                bare,
                find_theorem_def(stripped, bare).unwrap_or_else(|| {
                    panic!(
                        "{} does not define `theorem {}` (cited as {})",
                        cite.file, bare, cite.thm
                    )
                }),
            ),
        };
        let stack = namespace_stack_at(stripped, off, cite.file);
        let mut full = stack.join(".");
        if !full.is_empty() {
            full.push('.');
        }
        full.push_str(as_written);
        assert!(
            full == cite.thm || full.ends_with(&format!(".{}", cite.thm)),
            "citation `{}` is not a suffix of the resolved name `{}` in {}",
            cite.thm,
            full,
            cite.file
        );
        (full, off)
    }

    /// Comment-stripped source of a cited Lean file, cached per file.
    fn stripped_source<'a>(
        root: &std::path::Path,
        cache: &'a mut std::collections::HashMap<&'static str, String>,
        file: &'static str,
    ) -> &'a str {
        cache.entry(file).or_insert_with(|| {
            let path = root.join(file);
            let content = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("could not read {}: {}", path.display(), e));
            strip_lean_comments(&content)
        })
    }

    /// The statement of the theorem at `off`: from the `theorem` keyword to
    /// the first `:=`. In this repo's statement style every `¬`/`IConfluent`/
    /// `SegmentedIConfluent` token precedes the first `:=` (which is either a
    /// named argument like `(S := …)` — always AFTER the head symbol it
    /// belongs to — or the proof's own `:=`). A statement shape that hides a
    /// required token past the cut fails the polarity assertions loudly and
    /// gets this upgraded, not guessed around.
    fn statement_at<'a>(stripped: &'a str, off: usize, what: &str) -> &'a str {
        let rest = &stripped[off..];
        match rest.find(":=") {
            Some(i) => &rest[..i],
            None => panic!(
                "no `:=` after `theorem {}` — statement extraction needs an upgrade",
                what
            ),
        }
    }

    fn is_ident_char(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '_' || c == '\''
    }

    /// Byte offsets of standalone identifier occurrences of `token`.
    fn token_positions(text: &str, token: &str) -> Vec<usize> {
        let mut out = Vec::new();
        let mut start = 0;
        while let Some(pos) = text[start..].find(token) {
            let abs = start + pos;
            let before_ok = text[..abs].chars().last().map_or(true, |c| !is_ident_char(c));
            let after = abs + token.len();
            let after_ok = text[after..].chars().next().map_or(true, |c| !is_ident_char(c));
            if before_ok && after_ok {
                out.push(abs);
            }
            start = abs + token.len();
        }
        out
    }

    /// Is the token at `pos` negated — `¬` directly before it, looking
    /// through whitespace and opening parens?
    fn negated_at(text: &str, pos: usize) -> bool {
        text[..pos]
            .chars()
            .rev()
            .find(|c| !c.is_whitespace() && *c != '(')
            == Some('¬')
    }

    struct Polarity {
        positive_iconfluent: bool,
        negated_iconfluent: bool,
        segmented: bool,
    }

    fn statement_polarity(stmt: &str) -> Polarity {
        let mut p = Polarity {
            positive_iconfluent: false,
            negated_iconfluent: false,
            segmented: false,
        };
        for pos in token_positions(stmt, "IConfluent") {
            if negated_at(stmt, pos) {
                p.negated_iconfluent = true;
            } else {
                p.positive_iconfluent = true;
            }
        }
        p.segmented = !token_positions(stmt, "SegmentedIConfluent").is_empty();
        p
    }

    /// Every citation resolves to a real theorem in the cited file (through
    /// the file's actual namespace structure), and its keystone flag agrees
    /// with docs/MAP.md's ledger — in both directions. This is the gate
    /// GROKREVIEW §2.8 asked for: the check binary cannot disagree with the
    /// repo's curated ledger and stay green.
    #[test]
    fn citations_resolve_to_real_files_and_theorems() {
        let root = repo_root();
        let ledger = keystone_ledger(&root);
        let mut cache = std::collections::HashMap::new();
        for cite in all_citations() {
            let path = root.join(cite.file);
            assert!(
                path.is_file(),
                "citation names a missing file: {} — {}",
                cite.thm,
                cite.file
            );
            let stripped = stripped_source(&root, &mut cache, cite.file).to_string();
            let (_full, _off) = resolve_citation(&stripped, &cite);
            let module = cite
                .file
                .strip_prefix("Uwueave/")
                .and_then(|f| f.strip_suffix(".lean"))
                .unwrap_or_else(|| {
                    panic!(
                        "citation file is not of the form Uwueave/<Module>.lean: {}",
                        cite.file
                    )
                });
            let listed = ledger
                .iter()
                .any(|(n, m)| n == cite.thm && m == module);
            if cite.keystone {
                assert!(
                    listed,
                    "{} ({}) is NOT on docs/MAP.md's keystone ledger: either add \
                     its row there, or demote the citation to cite_unlisted!(...) \
                     so the output stops implying curation it does not have",
                    cite.thm, module
                );
            } else {
                assert!(
                    !listed,
                    "{} ({}) IS on docs/MAP.md's keystone ledger but the catalog \
                     still marks it [unlisted] — upgrade the citation to \
                     cite!(...) and let the output claim the row",
                    cite.thm, module
                );
            }
        }
    }

    /// Every verdict points the same direction as the Lean statements it
    /// cites — read from the source, not inferred from names.
    #[test]
    fn verdicts_match_the_lean_statements() {
        let root = repo_root();
        let mut cache = std::collections::HashMap::new();
        let mut polarity_of = |c: &Cite| -> Polarity {
            let stripped = stripped_source(&root, &mut cache, c.file).to_string();
            let (_full, off) = resolve_citation(&stripped, c);
            statement_polarity(statement_at(&stripped, off, c.thm))
        };
        for shape in ALL_SHAPES {
            for kind in ALL_KINDS {
                let Some(ruling) = classify(shape, kind) else {
                    continue;
                };
                let pair = format!("({}, {})", shape.token(), kind.token());
                let pols: Vec<(&Cite, Polarity)> =
                    ruling.cites.iter().map(|c| (c, polarity_of(c))).collect();
                match ruling.verdict {
                    Verdict::Free => {
                        for (c, p) in &pols {
                            assert!(
                                !p.negated_iconfluent,
                                "{} is FREE but cites {} whose statement negates IConfluent",
                                pair, c.thm
                            );
                            assert!(
                                !c.thm.contains("not_iconfluent"),
                                "{} is FREE but cites {}",
                                pair,
                                c.thm
                            );
                        }
                        assert!(
                            pols.iter().any(|(_, p)| p.positive_iconfluent),
                            "{} is FREE but no cited statement asserts IConfluent",
                            pair
                        );
                    }
                    Verdict::Escalates => {
                        assert!(
                            pols.iter().any(|(_, p)| p.negated_iconfluent),
                            "{} ESCALATES but no cited statement negates IConfluent",
                            pair
                        );
                    }
                    Verdict::Seam => {
                        assert!(
                            pols.iter().any(|(_, p)| p.negated_iconfluent),
                            "{} is SEAM but no cited statement negates IConfluent \
                             (the global failure half is missing)",
                            pair
                        );
                        assert!(
                            pols.iter().any(|(_, p)| p.segmented),
                            "{} is SEAM but no cited statement asserts \
                             SegmentedIConfluent (the seam half is missing)",
                            pair
                        );
                    }
                    Verdict::Pattern => {
                        for (c, p) in &pols {
                            assert!(
                                !p.negated_iconfluent,
                                "{} is PATTERN but cites {} whose statement negates IConfluent",
                                pair, c.thm
                            );
                            assert!(
                                !c.thm.contains("not_iconfluent"),
                                "{} is PATTERN but cites {}",
                                pair,
                                c.thm
                            );
                        }
                    }
                }
                for exit in ruling.exits {
                    for c in exit.cites {
                        let p = polarity_of(c);
                        assert!(
                            !p.negated_iconfluent,
                            "{} exit `{}` cites {} whose statement negates \
                             IConfluent — an exit must be a way OUT",
                            pair, exit.label, c.thm
                        );
                    }
                }
            }
        }
    }

    /// Same philosophy as the coverage pin: shrinking (or growing) the set of
    /// ledger-less citations is a conscious edit here, never a silent one.
    /// The per-citation flags themselves are enforced against docs/MAP.md by
    /// citations_resolve_to_real_files_and_theorems.
    #[test]
    fn unlisted_citation_count_is_pinned() {
        let unlisted = distinct_unlisted();
        let names: Vec<&str> = unlisted.iter().map(|c| c.thm).collect();
        assert_eq!(unlisted.len(), 9, "unlisted citations changed: {:?}", names);
    }

    /// The rendered output marks every ledger-less citation, and the footer
    /// claims exactly as much as the flags (themselves ledger-enforced) allow.
    #[test]
    fn output_marks_unlisted_citations_and_footer_tells_the_truth() {
        // A schema exercising every classified pair.
        let mut text = String::new();
        for shape in ALL_SHAPES {
            text.push_str(&format!(
                "field f_{}: {}\n",
                shape.token().replace('-', "_"),
                shape.token()
            ));
        }
        for shape in ALL_SHAPES {
            for kind in ALL_KINDS {
                if classify(shape, kind).is_some() {
                    text.push_str(&format!(
                        "invariant f_{}: {}\n",
                        shape.token().replace('-', "_"),
                        kind.token()
                    ));
                }
            }
        }
        let schema = parse_schema(&text).expect("generated schema parses");
        let report = render("all.schema", &schema);
        // Wrapping breaks lines at spaces; compare against a flattened copy.
        let flat = report.replace('\n', " ");
        let unlisted = distinct_unlisted();
        if unlisted.is_empty() {
            assert!(
                !report.contains("[unlisted]"),
                "no citation is unlisted, yet the output shows a marker"
            );
            assert!(flat.contains(LEDGER_FOOTER_CLEAN));
        } else {
            // Every unlisted citation is visibly marked in the verdict table
            // (table cells are never wrapped), with the literal marker text —
            // asserted against the string, not via cite_string, so dropping
            // the marker from the renderer cannot self-consistently pass.
            for c in &unlisted {
                assert!(
                    report.contains(&format!("{} [unlisted] — {}", c.thm, c.file)),
                    "unlisted citation not rendered with its marker: {} — {}",
                    c.thm,
                    c.file
                );
            }
            assert!(flat.contains("classification prose only"));
            assert!(
                !flat.contains("Every cited theorem is on docs/MAP.md"),
                "the footer claims a clean ledger while {} citation(s) lack rows",
                unlisted.len()
            );
        }
    }
}
