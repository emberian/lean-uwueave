/-
# Uwueave.ClashGraph — which finite graphs can really be clash graphs?

`CliqueLive.lean` correctly used the odd cycle `C₅` only as graph-theory
intuition: until a carrier and invariant realise it, the chromatic gap need not
be reachable by an I-confluence clash graph.  This file supplies the missing
realisation.

For every explicitly enumerated finite simple graph `G`, take the grow-only set
`Catalog.GSet V` and require its selected vertices to be an independent set of
`G`.  Every singleton is legal, and two singleton states clash exactly when
their vertices are adjacent.  Thus `G` is the induced clash graph on the
singleton states; this is an embedding theorem, not just a worked example.

The five-cycle fixture then has five real clash edges, five real non-edges, no
singleton triangle, and nevertheless forces at least three domains under every
global segmented certificate.  The last statement is proved directly from the
odd cycle, not inferred from an unproved graph-colouring fact.

The second half closes the general join-obstruction lemma left prose-only in
`CliqueLive.lean`: a finite list of legal leave-one-out joins that pairwise
merge to one illegal full join is a clique.  Its length therefore transports
to the existing exact segmented-width lower bound.  The `k = 3` constructor
re-derives `CliqueLive.triple_clash_forces_triangle`'s conclusion through the
general theorem.

Finiteness is explicit throughout.  `FiniteSimpleGraph.vertices` is supplied
by the caller with coverage and no-duplicates proofs; no universe-polymorphic
or infinite graph enumeration is claimed.
-/
import Uwueave.CliqueLive

namespace Uwueave.ClashGraph

open Uwueave Uwueave.Catalog Uwueave.SeamColoring Uwueave.Segmented

universe w

/-! ## §1 Every explicitly finite simple graph is a singleton clash graph. -/

/-- A finite simple graph with its enumeration exposed as data.  Symmetry and
irreflexivity are the only graph laws used by the embedding. -/
structure FiniteSimpleGraph (V : Type) where
  vertices : List V
  vertices_nodup : vertices.Nodup
  vertices_complete : ∀ v : V, v ∈ vertices
  adjacent : V → V → Bool
  adjacent_symm : ∀ x y, adjacent x y = adjacent y x
  adjacent_irrefl : ∀ x, adjacent x x = false

namespace FiniteSimpleGraph

/-- A singleton in the `GSet` carrier. -/
def singleton {V : Type} [DecidableEq V] (v : V) : GSet V :=
  fun x => decide (x = v)

@[simp] theorem singleton_apply {V : Type} [DecidableEq V] (v x : V) :
    singleton v x = true ↔ x = v := by
  simp [singleton]

/-- The independent-set invariant, stated propositionally against the explicit
vertex enumeration.  Coverage makes this the usual whole-graph definition. -/
def Independent {V : Type} (G : FiniteSimpleGraph V) : Invariant (GSet V) :=
  fun s => ∀ x ∈ G.vertices, ∀ y ∈ G.vertices,
    s x = true → s y = true → G.adjacent x y = false

/-- Executable form of `Independent`; only the caller-supplied enumeration is
searched. -/
def independentB {V : Type} (G : FiniteSimpleGraph V) (s : GSet V) : Bool :=
  G.vertices.all fun x =>
    G.vertices.all fun y => !(s x && s y && G.adjacent x y)

theorem independentB_eq_true_iff {V : Type} (G : FiniteSimpleGraph V)
    (s : GSet V) : independentB G s = true ↔ G.Independent s := by
  constructor
  · intro h x hx y hy hsx hsy
    have hxall := List.all_eq_true.mp h x hx
    have hyall := List.all_eq_true.mp hxall y hy
    cases he : G.adjacent x y with
    | false => rfl
    | true =>
      simp [hsx, he] at hyall
      rw [hsy] at hyall
      contradiction
  · intro h
    apply List.all_eq_true.mpr
    intro x hx
    apply List.all_eq_true.mpr
    intro y hy
    cases hsx : s x with
    | false => rfl
    | true =>
      cases hsy : s y with
      | false => rfl
      | true =>
        have he := h x hx y hy hsx hsy
        simp [he]

instance instDecidableIndependent {V : Type} (G : FiniteSimpleGraph V) :
    DecidablePred G.Independent :=
  fun s => decidable_of_iff (independentB G s = true)
    (independentB_eq_true_iff G s)

/-- Every singleton is independent: the only selected pair is `(v,v)`, and a
simple graph has no loop there. -/
theorem singleton_independent {V : Type} [DecidableEq V]
    (G : FiniteSimpleGraph V) (v : V) : G.Independent (singleton v) := by
  intro x _ y _ hx hy
  have hxv : x = v := (singleton_apply v x).mp hx
  have hyv : y = v := (singleton_apply v y).mp hy
  subst x
  subst y
  exact G.adjacent_irrefl v

/-- **THE EMBEDDING.** On singleton states, the independent-set clash relation
is exactly the supplied graph's adjacency relation.  Because the theorem is an
iff, it establishes both every requested edge and the absence of invented
chords. -/
theorem singleton_clashes_iff {V : Type} [DecidableEq V]
    (G : FiniteSimpleGraph V) (x y : V) :
    Clashes G.Independent (singleton x) (singleton y) ↔
      G.adjacent x y = true := by
  constructor
  · intro hc
    cases he : G.adjacent x y with
    | true => rfl
    | false =>
      exfalso
      apply hc.2.2
      intro a _ b _ ha hb
      change (singleton x a || singleton y a) = true at ha
      change (singleton x b || singleton y b) = true at hb
      have ha' : a = x ∨ a = y := by
        simpa [singleton] using ha
      have hb' : b = x ∨ b = y := by
        simpa [singleton] using hb
      rcases ha' with hax | hay
      · rcases hb' with hbx | hby
        · subst a; subst b; exact G.adjacent_irrefl x
        · subst a; subst b; exact he
      · rcases hb' with hbx | hby
        · subst a; subst b; rw [G.adjacent_symm]; exact he
        · subst a; subst b; exact G.adjacent_irrefl y
  · intro he
    refine ⟨singleton_independent G x, singleton_independent G y, ?_⟩
    intro hmerge
    have hxy := hmerge x (G.vertices_complete x) y (G.vertices_complete y)
      (by change (singleton x x || singleton y x) = true; simp [singleton])
      (by change (singleton x y || singleton y y) = true; simp [singleton])
    simp [he] at hxy

end FiniteSimpleGraph

/-! ## §2 An actual induced five-cycle. -/

/-- The five explicitly enumerable vertices of `C₅`. -/
inductive C5 where
  | v0 | v1 | v2 | v3 | v4
  deriving DecidableEq, Repr

open C5

def c5Vertices : List C5 := [v0, v1, v2, v3, v4]

def c5Adjacent : C5 → C5 → Bool
  | v0, v1 | v1, v0
  | v1, v2 | v2, v1
  | v2, v3 | v3, v2
  | v3, v4 | v4, v3
  | v4, v0 | v0, v4 => true
  | _, _ => false

/-- The executable five-cycle graph, including its exact finite enumeration. -/
def c5 : FiniteSimpleGraph C5 where
  vertices := c5Vertices
  vertices_nodup := by decide
  vertices_complete := by intro v; cases v <;> decide
  adjacent := c5Adjacent
  adjacent_symm := by intro x y; cases x <;> cases y <;> decide
  adjacent_irrefl := by intro x; cases x <;> decide

abbrev C5State := GSet C5

def c5Singleton (v : C5) : C5State := FiniteSimpleGraph.singleton v

def c5Independent : Invariant C5State := c5.Independent

instance : DecidablePred c5Independent :=
  FiniteSimpleGraph.instDecidableIndependent c5

/-- The fixture is the induced graph promised by the general embedding. -/
theorem c5_singleton_clashes_iff (x y : C5) :
    Clashes c5Independent (c5Singleton x) (c5Singleton y) ↔
      c5Adjacent x y = true :=
  FiniteSimpleGraph.singleton_clashes_iff c5 x y

/-- All five cycle edges are genuine clashes. -/
theorem c5_cycle_edges :
    Clashes c5Independent (c5Singleton v0) (c5Singleton v1)
    ∧ Clashes c5Independent (c5Singleton v1) (c5Singleton v2)
    ∧ Clashes c5Independent (c5Singleton v2) (c5Singleton v3)
    ∧ Clashes c5Independent (c5Singleton v3) (c5Singleton v4)
    ∧ Clashes c5Independent (c5Singleton v4) (c5Singleton v0) := by
  decide

/-- All five possible non-trivial chords are genuine non-clashes.  Together
with `c5_cycle_edges` this is an executable induced-`C₅` certificate. -/
theorem c5_has_no_chords :
    ¬ Clashes c5Independent (c5Singleton v0) (c5Singleton v2)
    ∧ ¬ Clashes c5Independent (c5Singleton v0) (c5Singleton v3)
    ∧ ¬ Clashes c5Independent (c5Singleton v1) (c5Singleton v3)
    ∧ ¬ Clashes c5Independent (c5Singleton v1) (c5Singleton v4)
    ∧ ¬ Clashes c5Independent (c5Singleton v2) (c5Singleton v4) := by
  decide

/-- No three singleton vertices form a clique: the realised cycle is not a
disguised triangle. -/
theorem c5_singletons_have_no_triangle (x y z : C5) :
    ¬ MenuTotality.Clique c5Independent
      [c5Singleton x, c5Singleton y, c5Singleton z] := by
  cases x <;> cases y <;> cases z <;>
    simp [MenuTotality.Clique, c5_singleton_clashes_iff, c5Adjacent]

private theorem fin_val_ne_of_ne {n : Nat} {x y : Fin n} (h : x ≠ y) :
    x.val ≠ y.val :=
  fun hv => h (Fin.eq_of_val_eq hv)

/-- **The odd-cycle floor.** Every globally valid seam for the independent-set
invariant needs at least three domains.  This lower bound does not come from a
3-clique (`c5_singletons_have_no_triangle` rules those out on the embedded
vertices); it is the real chromatic obstruction that `CliqueLive` could
previously only mention as external graph theory. -/
theorem c5_forces_three_domains {n : Nat}
    (h : LiveSegmented.GlobalWidth c5Independent n) : 3 ≤ n := by
  obtain ⟨σ, hσ⟩ := h
  have sep {x y : C5} (hc : Clashes c5Independent (c5Singleton x) (c5Singleton y)) :
      σ (c5Singleton x) ≠ σ (c5Singleton y) :=
    fun heq => hc.2.2 (hσ _ _ heq hc.1 hc.2.1).1
  have h01 := fin_val_ne_of_ne (sep c5_cycle_edges.1)
  have h12 := fin_val_ne_of_ne (sep c5_cycle_edges.2.1)
  have h23 := fin_val_ne_of_ne (sep c5_cycle_edges.2.2.1)
  have h34 := fin_val_ne_of_ne (sep c5_cycle_edges.2.2.2.1)
  have h40 := fin_val_ne_of_ne (sep c5_cycle_edges.2.2.2.2)
  have h0 := (σ (c5Singleton v0)).isLt
  have h1 := (σ (c5Singleton v1)).isLt
  have h2 := (σ (c5Singleton v2)).isLt
  have h3 := (σ (c5Singleton v3)).isLt
  have h4 := (σ (c5Singleton v4)).isLt
  omega

/-! ## §3 General finite leave-one-out obstructions. -/

/-- A proof-carrying finite `k`-wise join obstruction.  `leaves` are the
leave-one-out joins supplied by the caller; each is legal, every distinct
listed pair joins to the same `full` state, and that full state is illegal.

Storing the finite list is deliberate: this theorem does not claim to enumerate
an arbitrary carrier or synthesise the obstruction. -/
structure LeaveOneOutObstruction {S : Type w} [MergeState S]
    (I : Invariant S) where
  full : S
  leaves : List S
  leaves_legal : ∀ x ∈ leaves, I x
  pair_joins_full : leaves.Pairwise (fun x y => x ⊔ y = full)
  full_illegal : ¬ I full

private theorem pairwiseClashes_of_pairJoinsFull
    {S : Type w} [MergeState S] {I : Invariant S} {full : S} {leaves : List S}
    (hlegal : ∀ x ∈ leaves, I x)
    (hpairs : leaves.Pairwise (fun x y => x ⊔ y = full))
    (hbad : ¬ I full) : MenuTotality.Clique I leaves := by
  induction leaves with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
      have hp := List.pairwise_cons.mp hpairs
      refine List.Pairwise.cons ?_ ?_
      · intro b hb
        exact ⟨hlegal a List.mem_cons_self,
          hlegal b (List.mem_cons_of_mem a hb),
          by rw [hp.1 b hb]; exact hbad⟩
      · exact ih (fun x hx => hlegal x (List.mem_cons_of_mem a hx)) hp.2

/-- Every finite leave-one-out obstruction is a clique of exactly the listed
size. -/
theorem LeaveOneOutObstruction.clique {S : Type w} [MergeState S]
    {I : Invariant S} (h : LeaveOneOutObstruction I) :
    MenuTotality.Clique I h.leaves :=
  pairwiseClashes_of_pairJoinsFull h.leaves_legal h.pair_joins_full h.full_illegal

/-- The exact global segmented-width consequence: `k` supplied leave-one-out
states force at least `k` coordination domains. -/
theorem LeaveOneOutObstruction.forces_domains {S : Type w} [MergeState S]
    {I : Invariant S} (h : LeaveOneOutObstruction I) {n : Nat}
    (hw : LiveSegmented.GlobalWidth I n) : h.leaves.length ≤ n :=
  CliqueLive.clique_forces_global_width h.clique hw

/-- The three-generator instance of the general finite obstruction. -/
def tripleLeaveOneOut {S : Type w} [MergeState S] {I : Invariant S}
    (x y z : S) (hxy : I (x ⊔ y)) (hxz : I (x ⊔ z))
    (hyz : I (y ⊔ z)) (hbad : ¬ I ((x ⊔ y) ⊔ z)) :
    LeaveOneOutObstruction I where
  full := (x ⊔ y) ⊔ z
  leaves := [x ⊔ y, x ⊔ z, y ⊔ z]
  leaves_legal := by
    intro s hs
    simp at hs
    rcases hs with rfl | rfl | rfl
    · exact hxy
    · exact hxz
    · exact hyz
  pair_joins_full := by
    refine List.Pairwise.cons ?_
      (List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil))
    · intro s hs
      simp at hs
      rcases hs with rfl | rfl
      · exact join_xy_xz x y z
      · exact join_xy_yz x y z
    · intro s hs
      have hs' : s = y ⊔ z := by simpa using hs
      subst s
      exact join_xz_yz x y z
  full_illegal := hbad

/-- `CliqueLive.triple_clash_forces_triangle` recovered at `k = 3`, through the
general leave-one-out theorem rather than a triangle-specific clash proof. -/
theorem triple_clash_forces_triangle_via_leave_one_out
    {S : Type w} [MergeState S] {I : Invariant S} {x y z : S}
    (hxy : I (x ⊔ y)) (hxz : I (x ⊔ z)) (hyz : I (y ⊔ z))
    (hbad : ¬ I ((x ⊔ y) ⊔ z)) :
    MenuTotality.Clique I [x ⊔ y, x ⊔ z, y ⊔ z] :=
  (tripleLeaveOneOut x y z hxy hxz hyz hbad).clique

/-- The corresponding exact three-domain floor, now an instance of the general
`leaves.length` theorem. -/
theorem triple_leave_one_out_forces_three_domains
    {S : Type w} [MergeState S] {I : Invariant S} {x y z : S} {n : Nat}
    (hxy : I (x ⊔ y)) (hxz : I (x ⊔ z)) (hyz : I (y ⊔ z))
    (hbad : ¬ I ((x ⊔ y) ⊔ z))
    (hw : LiveSegmented.GlobalWidth I n) : 3 ≤ n := by
  have h := (tripleLeaveOneOut x y z hxy hxz hyz hbad).forces_domains hw
  simpa using h

end Uwueave.ClashGraph
