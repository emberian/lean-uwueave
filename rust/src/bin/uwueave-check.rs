//! uwueave-check — look up merge-safety verdicts for a replicated schema.
//!
//! This tool makes the Lean verdict catalog in `Uwueave/` usable without
//! opening Lean: you describe your replicated fields and the invariants you
//! care about in a tiny line-based schema, and it answers — per invariant —
//! whether the merge can break it, citing the exact machine-checked theorem
//! that settles the question.
//!
//! It is a LOOKUP TABLE, not a checker. Every (shape, kind) entry below is
//! annotated with the theorem it cites, and the unit tests verify that every
//! cited file exists in the repo and actually contains the cited theorem.
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
const ESCALATION_WITNESS: Cite = Cite { thm: "escalation_witness", file: CONFLUENCE };

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
        Cite { thm: "escrow_local_bound_iconfluent", file: CATALOG },
        Cite { thm: "escrow_global_bound", file: CATALOG },
    ],
};

// thm: budget_segmented
const EXIT_SEAM: Exit = Exit {
    label: "segmented (re-allocation seam)",
    story: "run free within an allocation and coordinate only to change the \
            allocation — one invariant, both verdicts, with the seam named.",
    cites: &[Cite { thm: "budget_segmented", file: SEGMENTED }],
};

// thm: derived_view_sec (price: view_not_stable)
const EXIT_OPLOG: Exit = Exit {
    label: "op-log",
    story: "replicate the operations (a grow-only set, trivially free) and derive \
            the structure by deterministic replay that skips invariant-violating \
            ops. The honest price, also a theorem (view_not_stable): an older \
            remote op can retroactively un-apply an edit you watched happen.",
    cites: &[
        Cite { thm: "derived_view_sec", file: MOVE },
        Cite { thm: "view_not_stable", file: MOVE },
    ],
};

// thm: conflict_surfaces, resolution_is_a_write
const EXIT_MV: Exit = Exit {
    label: "multi-value register",
    story: "keep every non-superseded write and surface concurrent writes as a \
            visible conflict; resolving it is an ordinary write at a dominating \
            clock.",
    cites: &[
        Cite { thm: "conflict_surfaces", file: MVREGISTER },
        Cite { thm: "resolution_is_a_write", file: MVREGISTER },
    ],
};

// thm: lww_every_invariant_iconfluent
const EXIT_LWW: Exit = Exit {
    label: "LWW arbitration",
    story: "hold the value in a single last-writer-wins register: the join selects \
            one write, so no invariant on that one register can break — someone \
            loses, silently, and that is the trade.",
    cites: &[Cite { thm: "lww_every_invariant_iconfluent", file: CATALOG }],
};

// thm: per_user_activation_free, pi_iconfluent
const EXIT_PER_USER: Exit = Exit {
    label: "per-user",
    story: "scope the state per user (a keyed map): each user owns their own copy, \
            and whatever per-user invariant you keep lifts pointwise to the whole \
            map.",
    cites: &[
        Cite { thm: "per_user_activation_free", file: WEAVE },
        Cite { thm: "pi_iconfluent", file: CONFLUENCE },
    ],
};

// thm: causal_dag_free
const EXIT_GROUNDED: Exit = Exit {
    label: "content-addressed insertion (causal-dag)",
    story: "fix parents at creation and derive ids from content: every edge \
            descends in rank, which is free and implies acyclicity — no cycle \
            check at any replication scale.",
    cites: &[Cite { thm: "causal_dag_free", file: ACYCLICITY }],
};

// thm: orset_present_survives
const EXIT_ORSET_SCOPED: Exit = Exit {
    label: "scoped add-wins guarantee",
    story: "state the feature in the form that is actually true: presence through \
            a tag the other side has not tombstoned survives the merge. That \
            conditional is what \"add-wins\" means.",
    cites: &[Cite { thm: "orset_present_survives", file: ORSET_L }],
};

// thm: clset_present_iconfluent
const EXIT_CLSET: Exit = Exit {
    label: "causal-length set",
    story: "presence as counter parity is free per element; the arbitration is \
            baked in — a longer remote history wins the element.",
    cites: &[Cite { thm: "clset_present_iconfluent", file: ORSET_L }],
};

// thm: fork_evidence_iconfluent, no_unilateral_evidence
const EXIT_DETECT: Exit = Exit {
    label: "accountable detection",
    story: "prevention needs coordination, but detection is free: two signed \
            blocks at one slot are themselves the proof, the evidence survives \
            every future merge, and a replica holding one block frames nobody.",
    cites: &[
        Cite { thm: "fork_evidence_iconfluent", file: CAUSALITY },
        Cite { thm: "no_unilateral_evidence", file: CAUSALITY },
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
        Cite { thm: "lww_every_invariant_iconfluent", file: CATALOG },
        Cite { thm: "LWW.join_selects", file: CATALOG },
    ],
    story: None,
    note: Some(LWW_SINGLE_NOTE),
    exits: &[],
};

// thm: escrow_local_bound_iconfluent + budget_segmented (+ budget_not_iconfluent)
const QUOTA_SEAM: Ruling = Ruling {
    verdict: Verdict::Seam,
    cites: &[
        Cite { thm: "escrow_local_bound_iconfluent", file: CATALOG },
        Cite { thm: "budget_segmented", file: SEGMENTED },
        Cite { thm: "budget_not_iconfluent", file: SEGMENTED },
    ],
    story: Some(SEAM_STORY),
    note: None,
    exits: &[],
};

// thm: active_path_not_iconfluent
const ACTIVE_PATH_ESCALATES: Ruling = Ruling {
    verdict: Verdict::Escalates,
    cites: &[Cite { thm: "active_path_not_iconfluent", file: WEAVE }],
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
            cites: &[Cite { thm: "gset_mem_iconfluent", file: CATALOG }],
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
            cites: &[Cite { thm: "gset_notmem_iconfluent", file: CATALOG }],
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
            cites: &[Cite { thm: "gset_monotone_iconfluent", file: CATALOG }],
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
            cites: &[Cite { thm: "gset_atMostOne_not_iconfluent", file: CATALOG }],
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
            cites: &[Cite { thm: "gset_atMostOne_not_iconfluent", file: CATALOG }],
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
            cites: &[Cite { thm: "or_breaks_iconfluence", file: CATALOG }],
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
            cites: &[Cite { thm: "acyclicity_not_iconfluent", file: ACYCLICITY }],
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
            cites: &[Cite { thm: "gcounter_lowerBound_iconfluent", file: CATALOG }],
            story: None,
            note: Some("merge only raises counts, so a grow-only floor survives."),
            exits: &[],
        }),
        // thm: escrow_local_bound_iconfluent (the escrow carrier IS a G-Counter)
        (GCounter, Ceiling) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[Cite { thm: "escrow_local_bound_iconfluent", file: CATALOG }],
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
            cites: &[Cite { thm: "pncounter_nonneg_not_iconfluent", file: CATALOG }],
            story: Some(PN_BALANCE_STORY),
            note: None,
            exits: &[EXIT_ESCROW, EXIT_SEAM],
        }),
        // thm: pncounter_nonneg_not_iconfluent (the proved instance is 0 ≤ net)
        (PnCounter, LowerBound) => Some(Ruling {
            verdict: Verdict::Escalates,
            cites: &[Cite { thm: "pncounter_nonneg_not_iconfluent", file: CATALOG }],
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
            cites: &[Cite { thm: "lww_cross_field_not_iconfluent", file: CATALOG }],
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
                Cite { thm: "per_user_activation_free", file: WEAVE },
                Cite { thm: "pi_iconfluent", file: CONFLUENCE },
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
            cites: &[Cite { thm: "gset_mem_iconfluent", file: CATALOG }],
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
                Cite { thm: "conflict_surfaces", file: MVREGISTER },
                Cite { thm: "view_antichain", file: MVREGISTER },
                Cite { thm: "resolution_is_a_write", file: MVREGISTER },
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
            cites: &[Cite { thm: "orset_present_not_iconfluent", file: ORSET_L }],
            story: Some(
                "Both replicas have seen the element added under tags t1 and t2. \
                 Replica A removes what it observed and tombstones t2 — still alive \
                 through t1; replica B symmetrically tombstones t1 — alive through \
                 t2. Each replica shows the element present, but the merge holds \
                 both tombstones, and the element is gone.",
            ),
            note: Some(
                "honesty note from the Lean: under causal delivery of operations \
                 this witness pair may not be jointly reachable; op-based OR-Sets \
                 narrow the state space and state their guarantee in the scoped, \
                 conditional form (orset_present_survives).",
            ),
            exits: &[EXIT_ORSET_SCOPED, EXIT_CLSET],
        }),

        // ------------------------------------------------------------ clset
        // thm: clset_present_iconfluent
        (ClSet, Member) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[Cite { thm: "clset_present_iconfluent", file: ORSET_L }],
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
            cites: &[Cite { thm: "clset_absent_iconfluent", file: ORSET_L }],
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
            cites: &[Cite { thm: "clset_cross_element_not_iconfluent", file: ORSET_L }],
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
            cites: &[Cite { thm: "gcounter_lowerBound_iconfluent", file: CATALOG }],
            story: None,
            note: Some("the escrow carrier is a G-Counter; a grow-only floor survives."),
            exits: &[],
        }),
        // thm: escrow_local_bound_iconfluent (+ escrow_global_bound)
        (Escrow, Ceiling) => Some(Ruling {
            verdict: Verdict::Free,
            cites: &[
                Cite { thm: "escrow_local_bound_iconfluent", file: CATALOG },
                Cite { thm: "escrow_global_bound", file: CATALOG },
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
                Cite { thm: "escrow_local_bound_iconfluent", file: CATALOG },
                Cite { thm: "escrow_global_bound", file: CATALOG },
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
            cites: &[Cite { thm: "gset_mem_iconfluent", file: CATALOG }],
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
            cites: &[Cite { thm: "gset_monotone_iconfluent", file: CATALOG }],
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
            cites: &[Cite { thm: "gset_atMostOne_not_iconfluent", file: CATALOG }],
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
                Cite { thm: "causal_dag_free", file: ACYCLICITY },
                Cite { thm: "grounded_iconfluent", file: ACYCLICITY },
                Cite { thm: "grounded_acyclic", file: ACYCLICITY },
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
            cites: &[Cite { thm: "gset_mem_iconfluent", file: CATALOG }],
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
                Cite { thm: "derived_view_sec", file: MOVE },
                Cite { thm: "miniInterp_acyclic", file: MOVE },
                Cite { thm: "view_not_stable", file: MOVE },
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
    format!("{} — {}", c.thm, c.file)
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

    /// Every citation used anywhere in the table (rulings and exits alike).
    fn every_citation() -> Vec<Cite> {
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

    fn file_defines_theorem(content: &str, name: &str) -> bool {
        let needle = format!("theorem {}", name);
        let mut start = 0;
        while let Some(pos) = content[start..].find(&needle) {
            let after = start + pos + needle.len();
            let boundary = match content[after..].chars().next() {
                None => true,
                Some(c) => !(c.is_ascii_alphanumeric() || c == '_' || c == '\''),
            };
            if boundary {
                return true;
            }
            start = after;
        }
        false
    }

    #[test]
    fn citations_resolve_to_real_files_and_theorems() {
        // Walk up from CARGO_MANIFEST_DIR (rust/) to the repo root — the
        // directory that contains Uwueave/.
        let mut root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        loop {
            if root.join("Uwueave").is_dir() {
                break;
            }
            assert!(
                root.pop(),
                "no directory containing Uwueave/ above CARGO_MANIFEST_DIR"
            );
        }
        for cite in every_citation() {
            let path = root.join(cite.file);
            assert!(
                path.is_file(),
                "citation names a missing file: {} — {}",
                cite.thm,
                cite.file
            );
            let content = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("could not read {}: {}", path.display(), e));
            // `LWW.join_selects` lives in a namespace; grep its bare name.
            let bare = cite.thm.rsplit('.').next().unwrap();
            assert!(
                file_defines_theorem(&content, bare),
                "{} does not define `theorem {}` (cited as {})",
                cite.file,
                bare,
                cite.thm
            );
        }
    }
}
