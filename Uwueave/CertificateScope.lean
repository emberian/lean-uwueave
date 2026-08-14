/-
# Uwueave.CertificateScope — the future-sufficient key, and what may be reused by it.

**Origin: codex's third review.** The first produced `Evidence.lean`'s two
corrections; the second produced `WorldFuture.lean` (a future is indexed by the
world, not by the state) — and this library's answer to *its* remedy was a
refutation: `WorldFuture.frontier_and_epoch_do_not_separate` shows the two
witness worlds agree on frontier, held certificates, roster **and** epoch, so
"index by the frontier or the epoch" is not the repair. `HistoryBase.
the_base_scope_repairs_the_state_keyed_certificate` then showed the *same*
state-keyed certificate is sound scoped to the base it was computed against and
unsound scoped to the history root.

Codex's third review reads those three results as instances of one unbuilt
abstraction, and asks for it:

> The abstraction is not "frontier-indexed" or "base-indexed". It is a
> **future-sufficient key**. For an evaluator `e` and future relation `F`,
> define `Residual(w) = { e t | F w t }`. A key `κ : World → K` is SUFFICIENT
> when `κ w = κ v → Residual w = Residual v`. Only then may an exactness
> certificate be reused by key equality. This is `MinimalSummary` lifted from
> merge contexts to future contexts. The coarsest sound certificate scope is
> the quotient by equality of residual-result sets. A history base, a full
> delivery pool, or a sealed epoch may each implement a sufficient key for
> particular evaluators; none should be privileged universally.

§1–§4 build it, §5–§6 exercise it in both directions on the objects the three
files already own, §7 checks the identification with `MinimalSummary`, and §8 is
the table. Nothing in `MinimalSummary.lean`, `WorldFuture.lean`,
`HistoryBase.lean` or `Evidence.lean` is edited; every connection below is a
theorem.

## What landed

  * **`Residual`, `ResidualEq`, `SufficientKey`, and the quotient** (§1–§3),
    with the universal property: `resQuot_coarsest_sufficient` — the class map
    is sufficient and every sufficient key refines it, `resFactor_spec`
    exhibiting the factoring map. ⚠ It lands, and it is **cheap**: see §7.
  * **Stability is a property of the residual alone.** `freeTermination_iff_
    residual` rewrites `Evidence.FreeTermination` as "the residual seals to the
    present answer" — literally `Holes.SealsTo` of the residual set
    (`freeTermination_iff_sealsTo_residualSet`), and, at a world with the
    reflexive future, "the residual is a subsingleton"
    (`freeTermination_iff_residual_subsingleton`), which needs no access to the
    present answer at all. That is *why* a key can license reuse.
  * **The licence and the prohibition** (§4). `key_licenses_reuse`: equal
    sufficient keys transport free termination. `no_sound_key_cert_accepts`:
    where a key glues a stable world to an unstable one, **every** sound
    key-indexed certificate must refuse that key — and `WorldFuture.
    no_sound_state_cert_accepts_openW` is re-derived from it
    (`no_sound_state_cert_accepts_openW_via_keys`), with `WorldFuture.
    StateCertSound` shown to *be* `KeyCertSound` at `observe` by `Iff.rfl`.
  * **The four witnesses codex asked for** (§5–§6):
      - `frontierEpoch_not_sufficient` — frontier+held+roster+epoch is
        INSUFFICIENT, riding `WorldFuture.frontier_and_epoch_do_not_separate`;
      - `deliveryKey_sufficient` — the observation **together with** the pool is
        SUFFICIENT, for every evaluator that reads only the observation;
      - `root_scope_not_sufficient` — the history root scope is INSUFFICIENT;
      - `base_scope_sufficient` — the named base's scope is SUFFICIENT, and
        `stateKeyed_sound_at_its_base_via_keys` re-derives `HistoryBase`'s
        verdict from the general machinery rather than restating it.
  * ⚠ **Two corrections to the brief, both proved.** The *pool alone* is not a
    sufficient key (`pool_not_sufficient`) — `wPending` and `wDelivered` share a
    pool and have different residuals; what is sufficient is `(observe, pool)`.
    And the *epoch is droppable*: `deliveryKey_drops_the_epoch` exhibits two
    distinct worlds with the same delivery key. So the key is exactly "what I
    hold, and what exists to be delivered", with the epoch out and the pool in —
    the sharp complement of `frontier_and_epoch_do_not_separate`.
  * **Sufficiency is evaluator-relative, and provably so.**
    `sufficient_for_every_evaluator_iff_injective` proves codex's "none should
    be privileged universally" in its strongest form: a key is sufficient for
    *every* evaluator and future relation **iff** it is injective. The epoch,
    useless for the rendered view, is a sufficient key for the epoch evaluator
    on wellformed worlds (`epoch_sufficient_on_wellformed`).

## The `MinimalSummary` identification: same shape, and NOT the same construction

Codex asserts the two are one construction at different indices. §7 checks it
and the answer is split, both halves proved:

  * **Same shape.** Both are the kernel of an observation:
    `sufficientKey_iff_sufficientFor` and `sufficient_iff_sufficientFor` show
    `SufficientKey κ e F ↔ SufficientFor κ (Residual e F)` and
    `Sufficient g f ↔ SufficientFor g (ctxObs f)`. The universal property is the
    same one-line kernel factorisation at both indices — which is also why it is
    cheap here, and why §3 claims nothing more than the partition order.
  * ⚠ **Different observation, and the difference is strict.** `MinimalSummary`
    observes the context-*indexed* function `z ↦ f (x ⊔ z)`; a residual observes
    only its **image**. `residual_mergeFuture_image` proves the second is the
    image of the first, and `residual_key_is_strictly_coarser_than_ctxEquiv`
    exhibits the collapse at `MinimalSummary`'s own pole: `sawA` and `sawB` have
    **equal residuals** and are **not** contextually equivalent.
  * ⚠ **`MinimalSummary`'s load-bearing lemma has no analogue.**
    `ctxEquiv_join` is what makes `CtxQuot` a lattice and the class map a
    `JoinHom` — "sufficiency and mergeability never trade off".
    `residual_is_not_a_join_congruence` refutes the corresponding statement:
    `sawA ≈ sawB` residually while `sawA ⊔ sawA` and `sawB ⊔ sawA` are
    separated. So `ResQuot` carries no merge — and at that same pole
    `residual_key_not_a_sufficient_summary` proves the residual key is not a
    sufficient summary for the count at all.
  * The reason is not incidental: a certificate asks *will the answer move*,
    which reads only the residual set; a summary asks *can I still compute the
    answer later*, which needs the indexing. Each construction is right for its
    own question.

## Honest boundary

⟨TERMINAL⟩ = a theorem of this model; ⟨UNDONE U-0007⟩ = work wearing a caveat's clothes.

  * ⟨TERMINAL⟩ **The universal property is cheap here, and is stated as such.**
    "Coarsest" means terminal in the partition order and nothing else: no bound
    on the bits a class takes, no decidability, no encoding — `MinimalSummary`'s
    representation boundary, inherited verbatim. What `MinimalSummary` earned
    with `ctxEquiv_join` and this file cannot earn is the *lattice*; §7 refutes
    it rather than omitting it.
  * ⟨TERMINAL⟩ **A key licenses REUSE, not verification.** `sufficient_key_
    need_not_license` (the identity key is sufficient and licenses nothing) and
    `sound_certificate_need_not_be_a_sufficient_key` (quiescence is sound and is
    not a key) are the two halves. A sufficient key plus one honest verification
    is what buys a reusable certificate (`verifiedAt_sound_of_sufficientKeyOn`).
  * ⟨TERMINAL⟩ **The reflexive-future side condition is load-bearing**, not
    bookkeeping: `the_reflexivity_side_condition_is_load_bearing` exhibits a
    three-world carrier where a sufficient key relates a stable world to an
    unstable one because the unstable one has no future of itself. At
    `World α` the condition is `Wf` (`WorldFuture.delivery_refl`), which
    `WorldFuture.lean` already carries as a hypothesis and not an invariant.
  * ⟨DONE U-0008⟩ **ERA placement is downstream and delivery-scoped.**
    `EraCertificate.era_finalisation_is_a_sound_certificate` transports ERA's
    finalised view into this file's `KeyCertSound` vocabulary, while
    `EraCertificate.eraKey_sufficient_on_wf` supplies the exact reusable key on
    wellformed worlds. `EraCertificate.era_stops_before_quiescence` witnesses
    the payoff: the finalised view can stop under delivery while the full view
    cannot. This does not identify `World.epoch` with an arbiter cut or verify a
    trusted seal; the placement lives on ERA's separate carrier and freezes the
    announcement axis.
  * ⟨TERMINAL⟩ **`Evidence.Closed` licenses values; closure plus a known roster
    licenses the view.** `closed_licenses_the_values` proves the first statement,
    while `closed_is_not_a_sound_delivery_certificate` refutes closure alone
    for `render`. `closed_and_rosterKnown_licenses_render` proves the exact
    repair: a known roster turns every delivery into an `Evidence.SealedFuture`,
    and `Evidence.render_congr` transports stability of `(values, Closed)` to
    the rendered view.
  * ⟨SCOPE U-0009 outside finite context-indexed query families⟩ **One residual
    evaluator at a time.** `ContextCompiler` now constructs the common
    refinement for a finite homogeneous family of merge-context-indexed
    queries. That is not this file's residual construction: a residual forgets
    which future produced an answer and keeps only the image. Common refinements
    of arbitrary future relations, residual images, heterogeneous queries, or
    infinite evaluator families remain unstated.
  * ⟨SCOPE U-0010 beyond a supplied finite contextual compiler⟩ **The witnesses
    are witnesses.** §5's separations are the three worlds `WorldFuture.lean`
    built. `ContextCompiler.sameClass` decides equality of its own finite,
    context-indexed signature and `sufficient_refines_signature` proves that
    key's partition property. Neither theorem decides whether an arbitrary key
    preserves this file's residual images. No theorem here characterises every
    world-pair a given residual key glues, and general key sufficiency remains
    undecidable by this development.
  * ⟨DONE downstream across the evidence/world universe chain⟩ **The former
    `Type 0` boundary is gone.** `Evidence`, `Holes`, `WorldFuture`, histories,
    and this file's certificate and residual bridges accept independent
    higher-universe carriers. `tests/DebtClosures/U_0011.lean` compiles the full
    mixed `Type 0`/`Type 1`/`Type 2` canary rather than inferring polymorphism
    from one isolated declaration.

Literature: the residual is Nerode's right congruence with futures in place of
word suffixes, exactly as `MinimalSummary`'s relation is with merge contexts —
the two differ in whether the context is remembered or only its image is
(Myhill–Nerode against a bare reachable-answer collapse). Free Termination
(Power–Koutris–Hellerstein, arXiv:2502.00222) supplies the stability question;
Timely's frontier (Brun et al., ITP 2021) is the pool the key must carry.
-/
import Uwueave.HistoryBase
import Uwueave.MinimalSummary

namespace Uwueave.CertificateScope

universe u v w x uW uR uA uV

open Uwueave Uwueave.Catalog Uwueave.Histories

/-! ## §1. The residual — what an evaluator may still say.

`Residual e F w` is codex's `{ e t | F w t }`, as a predicate on results rather
than a `Set` (this library has no `Set`). Everything about certificates below is
a statement about this object, and §1's job is to show that is not a change of
subject: free termination — `Evidence.lean`'s stability notion, the Free
Termination paper's Def. 3 — **is** a statement about the residual. -/

/-- **The residual result set.** The answers the evaluator `e` may still give
from `w`, along the future relation `F`. -/
def Residual {W : Type u} {R : Type v} (e : W → R) (F : W → W → Prop)
    (w : W) : R → Prop :=
  fun r => ∃ t, F w t ∧ e t = r

/-- The present answer is in the residual whenever the present is a future of
itself. ⚠ This is a hypothesis, not a fact: `WorldFuture.DeliveryFuture` is
reflexive only at **wellformed** worlds. -/
theorem residual_self {W : Type u} {R : Type v} (e : W → R) (F : W → W → Prop) {w : W}
    (h : F w w) : Residual e F w (e w) := ⟨w, h, rfl⟩

/-- **Equality of residuals**, pointwise, so that no `propext` is needed to
state it. `residualEq_iff_eq` gives codex's set-equality form. -/
def ResidualEq {W : Type u} {R : Type v} (e : W → R) (F : W → W → Prop)
    (w v : W) : Prop :=
  ∀ r, Residual e F w r ↔ Residual e F v r

theorem residualEq_refl {W : Type u} {R : Type v} (e : W → R) (F : W → W → Prop) (w : W) :
    ResidualEq e F w w := fun _ => Iff.rfl

theorem residualEq_symm {W : Type u} {R : Type v} {e : W → R} {F : W → W → Prop} {w v : W}
    (h : ResidualEq e F w v) : ResidualEq e F v w := fun r => (h r).symm

theorem residualEq_trans {W : Type u} {R : Type v} {e : W → R} {F : W → W → Prop}
    {w v u : W}
    (h₁ : ResidualEq e F w v) (h₂ : ResidualEq e F v u) : ResidualEq e F w u :=
  fun r => (h₁ r).trans (h₂ r)

/-- Residual equality is an equivalence relation — the setoid §3 quotients by. -/
theorem residualEq_equivalence {W : Type u} {R : Type v} (e : W → R)
    (F : W → W → Prop) :
    Equivalence (ResidualEq e F) :=
  ⟨residualEq_refl e F, residualEq_symm, residualEq_trans⟩

/-- The pointwise form and codex's set form agree — one `funext`/`propext`. -/
theorem residualEq_iff_eq {W : Type u} {R : Type v} (e : W → R)
    (F : W → W → Prop) (w v : W) :
    ResidualEq e F w v ↔ Residual e F w = Residual e F v := by
  constructor
  · intro h
    funext r
    exact propext (h r)
  · intro h r
    rw [h]

/-- **Free termination is a statement about the residual**: every answer still
reachable is the answer already given. This is `Evidence.FreeTermination`
unfolded through `Residual`, and it is what lets a *key* on residuals decide a
*stability* question. -/
theorem freeTermination_iff_residual {W : Type uW} {R : Type uR} (F : Evidence.Future W)
    (e : W → R) (w : W) :
    Evidence.FreeTermination F e w ↔ ∀ r, Residual e F w r → r = e w := by
  constructor
  · rintro h r ⟨t, ht, rfl⟩
    exact h t ht
  · intro h t ht
    exact h (e t) ⟨t, ht, rfl⟩

/-- The residual as a `Holes.Partial` — classical, for `Holes.truth`'s reason,
and used only for the bridge below. -/
noncomputable def residualSet {W : Type u} {R : Type uR} (e : W → R) (F : W → W → Prop)
    (w : W) : Holes.Partial R :=
  fun r => Holes.truth (Residual e F w r)

/-- **`Holes.SealsTo` is the shape of stability, exactly.** A replica is
free-terminating for `e` precisely when its residual set *seals to* the answer
it already holds — the same predicate `Holes.lean` §6 uses for "this is *the*
answer", now applied to the set of answers the future may still produce. -/
theorem freeTermination_iff_sealsTo_residualSet {W : Type uW} {R : Type uR} (F : Evidence.Future W)
    (e : W → R) (w : W) :
    Evidence.FreeTermination F e w ↔ Holes.SealsTo (residualSet e F w) (e w) := by
  rw [freeTermination_iff_residual]
  constructor
  · intro h r hr
    exact h r (Holes.truth_eq_true.mp hr)
  · intro h r hr
    exact h r (Holes.truth_eq_true.mpr hr)

/-- ⚠ **Stability needs no access to the present answer.** At a world that is a
future of itself, free termination is "the residual has at most one element" —
a property of the residual **alone**. That is the whole reason a key on
residuals can license a certificate: the certificate never has to carry the
answer it was verified against. -/
theorem freeTermination_iff_residual_subsingleton {W : Type uW} {R : Type uR}
    {F : Evidence.Future W} {e : W → R} {w : W} (hrefl : F w w) :
    Evidence.FreeTermination F e w
      ↔ ∀ r r', Residual e F w r → Residual e F w r' → r = r' := by
  constructor
  · intro h r r' hr hr'
    rw [(freeTermination_iff_residual F e w).mp h r hr,
      (freeTermination_iff_residual F e w).mp h r' hr']
  · intro h
    refine (freeTermination_iff_residual F e w).mpr (fun r hr => ?_)
    exact h r (e w) hr (residual_self e F hrefl)

/-! ## §2. Sufficient keys.

A key is a name a replica can file a verification under. It is **sufficient**
when equal names force equal residuals — which by §1 is exactly when equal names
force the same stability verdict. -/

/-- **A future-sufficient key.** Codex's definition: worlds with equal keys have
equal residuals for `e` along `F`. -/
def SufficientKey {W : Type u} {K : Type v} {R : Type w}
    (κ : W → K) (e : W → R) (F : W → W → Prop) :
    Prop :=
  ∀ w v, κ w = κ v → ResidualEq e F w v

/-- **A key sufficient on a domain.** The scope form: the key only has to
separate worlds *within* `D`. §6 shows a history base is exactly this — a base
names a set of versions, and the key is asked to be sufficient only there. -/
def SufficientKeyOn {W : Type u} {K : Type v} {R : Type w}
    (D : W → Prop) (κ : W → K) (e : W → R) (F : W → W → Prop) : Prop :=
  ∀ w v, D w → D v → κ w = κ v → ResidualEq e F w v

theorem sufficientKeyOn_of_sufficientKey {W : Type u} {K : Type v} {R : Type w}
    {D : W → Prop} {κ : W → K} {e : W → R} {F : W → W → Prop}
    (h : SufficientKey κ e F) :
    SufficientKeyOn D κ e F :=
  fun w v _ _ hk => h w v hk

/-- An injective key is sufficient for every evaluator and every future — it has
glued nothing. -/
theorem sufficientKey_of_injective {W : Type u} {K : Type v} {R : Type w}
    (κ : W → K) (e : W → R) (F : W → W → Prop)
    (hinj : ∀ w v, κ w = κ v → w = v) :
    SufficientKey κ e F := by
  intro w v hk
  rw [hinj w v hk]
  exact residualEq_refl e F v

/-- A key at least as fine as a sufficient one is sufficient. -/
theorem sufficientKey_of_refines {W : Type u} {K : Type v} {K' : Type w} {R : Type x}
    {κ : W → K} {κ' : W → K'} {e : W → R} {F : W → W → Prop}
    (h : SufficientKey κ e F)
    (hfine : ∀ w v, κ' w = κ' v → κ w = κ v) : SufficientKey κ' e F :=
  fun w v hk => h w v (hfine w v hk)

/-- ⚠ **NO KEY IS UNIVERSALLY SUFFICIENT EXCEPT AN INJECTIVE ONE.** Codex's
"none should be privileged universally", in its strongest form: a key that is
sufficient for *every* evaluator and *every* future relation has glued no two
worlds at all. So sufficiency is always a claim about a particular evaluator —
`epoch_sufficient_on_wellformed` beside `epoch_not_sufficient` is the same fact
with two evaluators at one key. -/
theorem sufficient_for_every_evaluator_iff_injective {W : Type u} {K : Type v}
    (κ : W → K) :
    (∀ (R : Type uR) (e : W → R) (F : W → W → Prop), SufficientKey κ e F)
      ↔ ∀ w v, κ w = κ v → w = v := by
  constructor
  · intro h w v hk
    let e : W → ULift.{uR} Prop := fun x => ULift.up (x = w)
    have hres := h (ULift.{uR} Prop) e (fun x y => x = y) w v hk
    obtain ⟨t, ht, heq⟩ := (hres (e w)).mp ⟨w, rfl, rfl⟩
    have hprop : (t = w) = (w = w) := congrArg ULift.down heq
    rw [← ht] at hprop
    exact (cast hprop.symm (rfl : w = w)).symm
  · intro hinj R e F
    exact sufficientKey_of_injective κ e F hinj

/-! ## §3. The quotient — the coarsest sufficient key.

The construction codex names: quotient the worlds by equality of residuals. The
universal property holds, and §7 says plainly what it is worth. -/

/-- The setoid of residual equality. -/
def resSetoid {W : Type u} {R : Type v} (e : W → R) (F : W → W → Prop) : Setoid W :=
  ⟨ResidualEq e F, residualEq_equivalence e F⟩

/-- **The coarsest sufficient key's codomain**: worlds modulo "the same answers
may still be given". -/
def ResQuot {W : Type u} {R : Type v} (e : W → R) (F : W → W → Prop) : Type u :=
  Quotient (resSetoid e F)

/-- The class map — the key this file proposes filing certificates under. -/
def resKey {W : Type u} {R : Type v} (e : W → R) (F : W → W → Prop)
    (w : W) : ResQuot e F :=
  Quotient.mk (resSetoid e F) w

theorem resKey_eq_iff {W : Type u} {R : Type v} (e : W → R) (F : W → W → Prop)
    (w v : W) :
    resKey e F w = resKey e F v ↔ ResidualEq e F w v :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- **The class map is a sufficient key** — `Quotient.exact`. -/
theorem resKey_sufficient {W : Type u} {R : Type v} (e : W → R) (F : W → W → Prop) :
    SufficientKey (resKey e F) e F :=
  fun _ _ h => Quotient.exact h

/-- **Every sufficient key refines the quotient**: no sufficient key glues two
classes the quotient keeps apart. -/
theorem sufficient_refines_resKey {W : Type u} {K : Type v} {R : Type w}
    {κ : W → K} {e : W → R} {F : W → W → Prop}
    (h : SufficientKey κ e F) (w v : W) (hk : κ w = κ v) :
    resKey e F w = resKey e F v :=
  Quotient.sound (h w v hk)

/-- The quotient's decoder: the residual itself descends to the classes. -/
def resResidual {W : Type u} {R : Type v} (e : W → R) (F : W → W → Prop) :
    ResQuot e F → (R → Prop) :=
  Quotient.lift (s := resSetoid e F) (Residual e F)
    (fun a b h => (residualEq_iff_eq e F a b).mp h)

@[simp] theorem resResidual_resKey {W : Type u} {R : Type v}
    (e : W → R) (F : W → W → Prop)
    (w : W) : resResidual e F (resKey e F w) = Residual e F w := rfl

open Classical in
/-- The map that factors the quotient through a sufficient key: read the class
off any world carrying the given key. Classical, and not an algorithm —
`MinimalSummary.ctxFactor`'s caveat verbatim. -/
noncomputable def resFactor {W : Type u} {K : Type v} {R : Type w} [Inhabited W]
    (κ : W → K) (e : W → R) (F : W → W → Prop) (k : K) : ResQuot e F :=
  if h : ∃ w : W, κ w = k then resKey e F h.choose else resKey e F default

/-- **The factorisation.** For a sufficient key, the quotient map *is*
`resFactor κ e F ∘ κ`. With `sufficient_refines_resKey` this is the universal
property in full. -/
theorem resFactor_spec {W : Type u} {K : Type v} {R : Type w} [Inhabited W]
    {κ : W → K} {e : W → R} {F : W → W → Prop}
    (h : SufficientKey κ e F) (w : W) :
    resFactor κ e F (κ w) = resKey e F w := by
  have hex : ∃ w' : W, κ w' = κ w := ⟨w, rfl⟩
  unfold resFactor
  rw [dif_pos hex]
  exact Quotient.sound (h hex.choose w hex.choose_spec)

/-- **THE UNIVERSAL PROPERTY.** The class map is a sufficient key, and every
sufficient key refines it: `ResQuot e F` is terminal among sufficient keys in
the partition order. ⚠ Two clauses, where `MinimalSummary.ctxQuot_coarsest_
sufficient` has three — the missing one is `JoinHom`, and §7's
`residual_is_not_a_join_congruence` shows it is missing because it is **false**
here, not because it was not attempted. -/
theorem resQuot_coarsest_sufficient {W : Type u} {R : Type v}
    (e : W → R) (F : W → W → Prop) :
    SufficientKey (resKey e F) e F
      ∧ ∀ (K : Type w) (κ : W → K), SufficientKey κ e F →
          ∀ w v : W, κ w = κ v → resKey e F w = resKey e F v :=
  ⟨resKey_sufficient e F, fun _ _ h w v hk => sufficient_refines_resKey h w v hk⟩

/-! ## §4. Certificate reuse — the licence and the prohibition.

A certificate is a value filed under a key; reuse is what happens when someone
else's key matches. §4 says exactly when that is sound and exactly when it is
prohibited, and the prohibition rides `WorldFuture.lean`'s refutation. -/

/-- **Sound**, for a key-indexed certificate: at every world whose key it
accepts, the evaluator really is free-terminating. The quantifier over worlds is
the reuse. -/
def KeyCertSound {W : Type uW} {R : Type uR} {K : Type u} (κ : W → K) (e : W → R) (F : W → W → Prop)
    (C : K → Prop) : Prop :=
  ∀ w, C (κ w) → Evidence.FreeTermination F e w

/-- The same, scoped to a domain — the shape a base scope takes (§6). -/
def KeyCertSoundOn {W : Type uW} {R : Type uR} {K : Type u} (D : W → Prop) (κ : W → K) (e : W → R)
    (F : W → W → Prop) (C : K → Prop) : Prop :=
  ∀ w, D w → C (κ w) → Evidence.FreeTermination F e w

/-- **THE LICENCE.** A verification transports along a sufficient key: if `w` is
free-terminating and `v` carries the same key, `v` is free-terminating too. The
side condition `F v v` is load-bearing — see
`the_reflexivity_side_condition_is_load_bearing`. -/
theorem key_licenses_reuse {W : Type uW} {R : Type uR} {K : Type u} {κ : W → K} {e : W → R}
    {F : W → W → Prop} (hsuf : SufficientKey κ e F) {w v : W}
    (hkey : κ w = κ v) (hv : F v v) (hw : Evidence.FreeTermination F e w) :
    Evidence.FreeTermination F e v := by
  have hres := hsuf w v hkey
  have hev : e v = e w := by
    obtain ⟨u, hu, heu⟩ := (hres (e v)).mpr ⟨v, hv, rfl⟩
    exact heu.symm.trans (hw u hu)
  intro t ht
  obtain ⟨u, hu, heu⟩ := (hres (e t)).mpr ⟨t, ht, rfl⟩
  rw [hev]
  exact heu.symm.trans (hw u hu)

/-- The licence, scoped. -/
theorem key_licenses_reuse_on {W : Type uW} {R : Type uR} {K : Type u}
    {D : W → Prop} {κ : W → K} {e : W → R} {F : W → W → Prop}
    (hsuf : SufficientKeyOn D κ e F) {w v : W}
    (hw : D w) (hv : D v) (hkey : κ w = κ v) (hrefl : F v v)
    (hstable : Evidence.FreeTermination F e w) : Evidence.FreeTermination F e v := by
  have hres := hsuf w v hw hv hkey
  have hev : e v = e w := by
    obtain ⟨u, hu, heu⟩ := (hres (e v)).mpr ⟨v, hrefl, rfl⟩
    exact heu.symm.trans (hstable u hu)
  intro t ht
  obtain ⟨u, hu, heu⟩ := (hres (e t)).mpr ⟨t, ht, rfl⟩
  rw [hev]
  exact heu.symm.trans (hstable u hu)

/-- **The certificate a replica actually files**: "I checked it here", filed
under its key. This is the object `WorldFuture.certificate_reuse_is_unsound` is
about, with the index left open. -/
def verifiedAt {W : Type uW} {R : Type uR} {K : Type u} (D : W → Prop) (κ : W → K) (e : W → R)
    (F : W → W → Prop) : K → Prop :=
  fun k => ∃ w, D w ∧ κ w = k ∧ Evidence.FreeTermination F e w

/-- **THE LICENCE, IN THE FORM A DEPLOYMENT USES.** Under a sufficient key, the
"I checked it here" certificate is sound — anyone whose key matches may use it,
and no further check is needed. This is the positive half of codex's "only then
may an exactness certificate be reused by key equality". -/
theorem verifiedAt_sound_of_sufficientKeyOn {W : Type uW} {R : Type uR} {K : Type u} {D : W → Prop}
    {κ : W → K} {e : W → R} {F : W → W → Prop}
    (hsuf : SufficientKeyOn D κ e F) (hrefl : ∀ w, D w → F w w) :
    KeyCertSoundOn D κ e F (verifiedAt D κ e F) := by
  intro v hDv hC
  obtain ⟨w, hDw, hkey, hw⟩ := hC
  exact key_licenses_reuse_on hsuf hDw hDv hkey (hrefl v hDv) hw

/-- ⚠ **THE PROHIBITION.** Where a key glues a world to an unstable one, **every**
sound certificate indexed by that key must refuse the key — including the one a
replica verified correctly. Not "is weaker": is prohibited from ever saying yes.
This is `WorldFuture.no_sound_state_cert_accepts_openW` with the index left
open, and the next theorem recovers that statement from this one. -/
theorem no_sound_key_cert_accepts {W : Type uW} {R : Type uR} {K : Type u} (κ : W → K) (e : W → R)
    (F : W → W → Prop) {w v : W} (hkey : κ w = κ v)
    (hbad : ¬ Evidence.FreeTermination F e v) (C : K → Prop)
    (hC : KeyCertSound κ e F C) : ¬ C (κ w) := by
  intro h
  rw [hkey] at h
  exact hbad (hC v h)

/-- **`WorldFuture.StateCertSound` IS `KeyCertSound` at the observation key** —
definitionally, so the general machinery is about the same object and not a
lookalike. -/
theorem stateCertSound_is_keyCertSound {α : Type uA} (C : WorldFuture.StateCert α) :
    WorldFuture.StateCertSound C
      ↔ KeyCertSound WorldFuture.observe (WorldFuture.renderW (α := α))
          WorldFuture.DeliveryFuture C :=
  Iff.rfl

/-- **…and `WorldFuture.WorldCertSound` is `KeyCertSound` at the identity key.**
The world index is the finest key there is, which is why it is sound and why it
is not reusable at any coarser name. -/
theorem worldCertSound_is_keyCertSound {α : Type uA} (C : WorldFuture.WorldCert α) :
    WorldFuture.WorldCertSound C
      ↔ KeyCertSound (fun w : WorldFuture.World α => w)
          (WorldFuture.renderW (α := α)) WorldFuture.DeliveryFuture C :=
  Iff.rfl

/-- **`WorldFuture.no_sound_state_cert_accepts_openW`, re-derived.** The general
prohibition, instantiated at `κ := observe` with `WorldFuture.lean`'s own
witness pair — same statement, obtained from the abstraction rather than
restated beside it. -/
theorem no_sound_state_cert_accepts_openW_via_keys (C : WorldFuture.StateCert Holes.Val)
    (hC : WorldFuture.StateCertSound C) : ¬ C Evidence.openW :=
  no_sound_key_cert_accepts WorldFuture.observe WorldFuture.renderW
    WorldFuture.DeliveryFuture WorldFuture.same_observation
    WorldFuture.not_stable_at_wPending C hC

/-! ### §4.1 The reflexivity side condition is load-bearing

Three worlds, no reflexive futures at two of them, and a sufficient key that
relates a stable world to an unstable one. So `key_licenses_reuse` cannot drop
`F v v` — and at `World α` that hypothesis is `WorldFuture.Wf`, which
`WorldFuture.lean` carries as a hypothesis and not as an invariant. -/

/-- A three-world carrier. -/
inductive Trio where
  /-- Stable: its only future agrees with it. -/
  | a
  /-- Unstable: its only future disagrees, and it is not a future of itself. -/
  | b
  /-- The common future. -/
  | c
  deriving DecidableEq, Repr

/-- Both `a` and `b` step only to `c`; nothing steps to itself. -/
def trioF : Evidence.Future Trio := fun x y => (x = .a ∨ x = .b) ∧ y = .c

/-- The evaluator: only `b` reads `true`. -/
def trioE : Trio → Bool
  | .a => false
  | .b => true
  | .c => false

/-- The key: `a` and `b` share a name. -/
def trioKey : Trio → Bool
  | .c => true
  | _ => false

theorem trio_residual_ab {x : Trio} (h : x = .a ∨ x = .b) (r : Bool) :
    Residual trioE trioF x r ↔ r = false := by
  constructor
  · rintro ⟨t, ⟨_, rfl⟩, rfl⟩
    rfl
  · rintro rfl
    exact ⟨.c, ⟨h, rfl⟩, rfl⟩

/-- The key really is sufficient: `a` and `b` have the same residual `{false}`. -/
theorem trioKey_sufficient : SufficientKey trioKey trioE trioF := by
  intro w v hk r
  cases w <;> cases v <;>
    first
      | exact Iff.rfl
      | exact absurd hk (by decide)
      | exact Iff.trans (trio_residual_ab (Or.inl rfl) r)
          (Iff.symm (trio_residual_ab (Or.inr rfl) r))
      | exact Iff.trans (trio_residual_ab (Or.inr rfl) r)
          (Iff.symm (trio_residual_ab (Or.inl rfl) r))

theorem trio_freeTermination_a : Evidence.FreeTermination trioF trioE .a := by
  rintro t ⟨_, rfl⟩
  rfl

theorem trio_not_freeTermination_b : ¬ Evidence.FreeTermination trioF trioE .b := by
  intro h
  exact absurd (h .c ⟨Or.inr rfl, rfl⟩) (by decide)

theorem trio_not_refl : ¬ trioF .b .b := by
  intro h
  exact absurd h.2 (by decide)

/-- ⚠ **The side condition cannot be dropped.** A sufficient key, two worlds
sharing it, one free-terminating and the other not — because the second is not a
future of itself, so its residual never mentions its own answer. -/
theorem the_reflexivity_side_condition_is_load_bearing :
    SufficientKey trioKey trioE trioF
      ∧ trioKey .a = trioKey .b
      ∧ Evidence.FreeTermination trioF trioE .a
      ∧ ¬ trioF .b .b
      ∧ ¬ Evidence.FreeTermination trioF trioE .b :=
  ⟨trioKey_sufficient, rfl, trio_freeTermination_a, trio_not_refl,
   trio_not_freeTermination_b⟩

/-! ## §5. The witnesses at the delivery index.

`WorldFuture.lean` built three worlds; §5 measures four candidate keys against
them. The residual computation at a quiesced world does all the work: a quiesced
world's residual is the single view it already renders. -/

open WorldFuture in
/-- **A quiesced world's residual is a singleton** — the view it already
renders. `WorldFuture.quiesced_render_stable` one way, `delivery_refl` the
other. -/
theorem residual_at_quiesced {α : Type uA} {w : World α} (hq : Quiesced w)
    (r : Evidence.View α) :
    Residual renderW DeliveryFuture w r ↔ r = renderW w := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact quiesced_render_stable hq t ht
  · rintro rfl
    exact ⟨w, delivery_refl (wf_of_quiesced hq), rfl⟩

theorem renderW_wQuiesced :
    WorldFuture.renderW WorldFuture.wQuiesced = Evidence.View.provisional 47 :=
  Evidence.four_states_inhabited.2.1

theorem renderW_wPending :
    WorldFuture.renderW WorldFuture.wPending = Evidence.View.provisional 47 :=
  Evidence.four_states_inhabited.2.1

theorem renderW_wDelivered :
    WorldFuture.renderW WorldFuture.wDelivered = Evidence.View.forkedOpen :=
  Evidence.render_openForkW

/-- `wDelivered` is quiesced: `bob`'s `49` has arrived and nothing else was
issued. -/
theorem quiesced_wDelivered : WorldFuture.Quiesced WorldFuture.wDelivered := rfl

theorem residual_wPending_forkedOpen :
    Residual WorldFuture.renderW WorldFuture.DeliveryFuture WorldFuture.wPending
      Evidence.View.forkedOpen :=
  ⟨WorldFuture.wDelivered, WorldFuture.delivery_wPending_wDelivered, renderW_wDelivered⟩

theorem residual_wPending_provisional :
    Residual WorldFuture.renderW WorldFuture.DeliveryFuture WorldFuture.wPending
      (Evidence.View.provisional 47) :=
  ⟨WorldFuture.wPending, WorldFuture.delivery_refl WorldFuture.wf_wPending,
   renderW_wPending⟩

/-- ⚠ **The witness pair has different residuals.** `wPending` may still render
`forkedOpen`; `wQuiesced`, with the identical materialized state, may render
only `provisional 47`. This is `WorldFuture.delivery_futures_differ` read at the
value level, and it is what every insufficiency verdict below rides on. -/
theorem residual_separates_quiesced_pending :
    ¬ ResidualEq WorldFuture.renderW WorldFuture.DeliveryFuture
        WorldFuture.wQuiesced WorldFuture.wPending := by
  intro h
  have hq := (residual_at_quiesced WorldFuture.quiesced_wQuiesced _).mp
    ((h Evidence.View.forkedOpen).mpr residual_wPending_forkedOpen)
  rw [renderW_wQuiesced] at hq
  exact absurd hq (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

/-- …and so do `wPending` and `wDelivered`, which share a **pool**. -/
theorem residual_separates_pending_delivered :
    ¬ ResidualEq WorldFuture.renderW WorldFuture.DeliveryFuture
        WorldFuture.wPending WorldFuture.wDelivered := by
  intro h
  have hq := (residual_at_quiesced quiesced_wDelivered _).mp
    ((h (Evidence.View.provisional 47)).mp residual_wPending_provisional)
  rw [renderW_wDelivered] at hq
  exact absurd hq (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

/-- …and so do the two **quiesced** worlds, which is why quiescence is not a
key. -/
theorem residual_separates_quiesced_delivered :
    ¬ ResidualEq WorldFuture.renderW WorldFuture.DeliveryFuture
        WorldFuture.wQuiesced WorldFuture.wDelivered := by
  intro h
  have h1 : Residual WorldFuture.renderW WorldFuture.DeliveryFuture
      WorldFuture.wQuiesced (WorldFuture.renderW WorldFuture.wQuiesced) :=
    (residual_at_quiesced WorldFuture.quiesced_wQuiesced _).mpr rfl
  have hq := (residual_at_quiesced quiesced_wDelivered _).mp ((h _).mp h1)
  rw [renderW_wQuiesced, renderW_wDelivered] at hq
  exact absurd hq (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

/-- Any key that glues the witness pair is insufficient for the rendered view. -/
theorem not_sufficient_of_glues_witness_pair {K : Type u}
    (κ : WorldFuture.World Holes.Val → K)
    (h : κ WorldFuture.wQuiesced = κ WorldFuture.wPending) :
    ¬ SufficientKey κ WorldFuture.renderW WorldFuture.DeliveryFuture :=
  fun hs => residual_separates_quiesced_pending (hs _ _ h)

/-- Any key that glues `wPending` to `wDelivered` is insufficient. -/
theorem not_sufficient_of_glues_pending_delivered {K : Type u}
    (κ : WorldFuture.World Holes.Val → K)
    (h : κ WorldFuture.wPending = κ WorldFuture.wDelivered) :
    ¬ SufficientKey κ WorldFuture.renderW WorldFuture.DeliveryFuture :=
  fun hs => residual_separates_pending_delivered (hs _ _ h)

/-- Any key that glues the two quiesced worlds is insufficient. -/
theorem not_sufficient_of_glues_quiesced_delivered {K : Type u}
    (κ : WorldFuture.World Holes.Val → K)
    (h : κ WorldFuture.wQuiesced = κ WorldFuture.wDelivered) :
    ¬ SufficientKey κ WorldFuture.renderW WorldFuture.DeliveryFuture :=
  fun hs => residual_separates_quiesced_delivered (hs _ _ h)

/-! ### §5.1 WITNESS ONE — frontier-plus-epoch is insufficient -/

/-- Codex's second remedy, as a key: the frontier, the certificates in hand, the
roster and the sealed epoch. Everything about the context **except** what has
been issued. -/
def frontierEpochKey {α : Type uA} (w : WorldFuture.World α) :
    GSet Evidence.Source × GSet Evidence.Source × GSet Evidence.Source × Nat :=
  (WorldFuture.frontier w, WorldFuture.held w, w.roster, w.epoch)

/-- The witness pair shares it — `WorldFuture.frontier_and_epoch_do_not_separate`,
collected into one key. -/
theorem frontierEpochKey_glues_the_pair :
    frontierEpochKey WorldFuture.wQuiesced = frontierEpochKey WorldFuture.wPending := by
  have h := WorldFuture.frontier_and_epoch_do_not_separate
  show (WorldFuture.frontier WorldFuture.wQuiesced, WorldFuture.held WorldFuture.wQuiesced,
      WorldFuture.wQuiesced.roster, WorldFuture.wQuiesced.epoch)
    = (WorldFuture.frontier WorldFuture.wPending, WorldFuture.held WorldFuture.wPending,
      WorldFuture.wPending.roster, WorldFuture.wPending.epoch)
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2.1]

/-- ⚠ **WITNESS ONE: frontier-plus-epoch is NOT a sufficient key.** The remedy
`WorldFuture.lean` refuted, refuted again in the vocabulary that says what is
wrong with it: the two worlds it glues have different residuals, so a
certificate reused across it is reused across a genuine change of future. -/
theorem frontierEpoch_not_sufficient :
    ¬ SufficientKey (frontierEpochKey (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture :=
  not_sufficient_of_glues_witness_pair _ frontierEpochKey_glues_the_pair

/-- **…and neither is the state key** — the original defect, in the same
vocabulary. -/
theorem observe_not_sufficient :
    ¬ SufficientKey (WorldFuture.observe (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture :=
  not_sufficient_of_glues_witness_pair _ WorldFuture.same_observation

/-- **…and neither is the epoch alone**, for the rendered view. -/
theorem epoch_not_sufficient :
    ¬ SufficientKey (fun w : WorldFuture.World Holes.Val => w.epoch)
        WorldFuture.renderW WorldFuture.DeliveryFuture :=
  not_sufficient_of_glues_witness_pair _ rfl

/-! ### §5.2 WITNESS TWO — the observation together with the pool is sufficient

⚠ And the brief's phrase needs one correction, which is proved rather than
noted: the **pool alone** is not a key (`pool_not_sufficient`). What is
sufficient is what the replica holds *together with* what exists to be
delivered. The epoch is provably droppable. -/

/-- **The delivery key**: what the replica has materialized, and the pool it
sits in. -/
def deliveryKey {α : Type uA} (w : WorldFuture.World α) :
    Evidence.ResultEvidence α × Evidence.ResultEvidence α :=
  (WorldFuture.observe w, WorldFuture.pool w)

/-- One inclusion of the residual transport: rebuild the future world over the
other world's context. The pool and the epoch of the rebuilt world are the
target's, and its observation is the source future's — which is all the
evaluator reads. -/
theorem deliveryKey_residual_sub {α : Type uA} {R : Type u}
    (q : Evidence.ResultEvidence α → R)
    {w v : WorldFuture.World α} (hobs : WorldFuture.observe w = WorldFuture.observe v)
    (hpool : WorldFuture.pool w = WorldFuture.pool v) (r : R) :
    Residual (fun u => q (WorldFuture.observe u)) WorldFuture.DeliveryFuture w r →
      Residual (fun u => q (WorldFuture.observe u)) WorldFuture.DeliveryFuture v r := by
  rintro ⟨t, ⟨hdf, _, _⟩, rfl⟩
  refine ⟨⟨t.state, v.issued, v.roster, v.sealed, v.epoch⟩, ⟨?_, rfl, rfl⟩, rfl⟩
  rw [← hpool, ← hobs]
  exact hdf

/-- ⚠ **WITNESS TWO: the observation and the pool are a sufficient key** — for
**every** evaluator that reads only the materialized state, which includes
`WorldFuture.renderW`. Two worlds agreeing on both may still differ (in their
epoch), and no such difference is visible to any answer delivery can produce. -/
theorem deliveryKey_sufficient {α : Type uA} {R : Type u}
    (q : Evidence.ResultEvidence α → R) :
    SufficientKey (deliveryKey (α := α)) (fun w => q (WorldFuture.observe w))
      WorldFuture.DeliveryFuture := by
  intro w v hk r
  have hobs : WorldFuture.observe w = WorldFuture.observe v := congrArg Prod.fst hk
  have hpool : WorldFuture.pool w = WorldFuture.pool v := congrArg Prod.snd hk
  exact ⟨deliveryKey_residual_sub q hobs hpool r,
    deliveryKey_residual_sub q hobs.symm hpool.symm r⟩

/-- The delivery key is sufficient for the rendered view. -/
theorem deliveryKey_sufficient_render {α : Type uA} :
    SufficientKey (deliveryKey (α := α)) (WorldFuture.renderW (α := α))
      WorldFuture.DeliveryFuture :=
  deliveryKey_sufficient Evidence.render

/-- `wQuiesced` with the producer's epoch advanced — same state, same pool. -/
def wQuiescedEpoch1 : WorldFuture.World Holes.Val :=
  { WorldFuture.wQuiesced with epoch := 1 }

/-- ⚠ **The delivery key is strictly coarser than the world.** It drops the
epoch, and the epoch is a real component of the world. So `deliveryKey_
sufficient` is not injectivity in disguise: the key genuinely quotients.

Set against `frontierEpoch_not_sufficient`, this pins the delivery index
exactly: **the pool is in, the epoch is out.** -/
theorem deliveryKey_drops_the_epoch :
    deliveryKey WorldFuture.wQuiesced = deliveryKey wQuiescedEpoch1
      ∧ WorldFuture.wQuiesced ≠ wQuiescedEpoch1 :=
  ⟨rfl, fun h => absurd (congrArg WorldFuture.World.epoch h) (by decide)⟩

/-- ⚠ **The pool alone is NOT a sufficient key.** `wPending` and `wDelivered`
sit in the same pool — `bob`'s `49` is issued in both — and one of them has
already delivered it. Their residuals differ, so "index by the delivery pool"
is not the repair either; the observation must ride along. -/
theorem pool_not_sufficient :
    ¬ SufficientKey (WorldFuture.pool (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture :=
  not_sufficient_of_glues_pending_delivered _ rfl

/-- **The epoch IS a sufficient key — for the epoch evaluator, on wellformed
worlds.** Delivery freezes the epoch, so the only epoch a wellformed world may
still report is the one it has. Beside `epoch_not_sufficient` this is codex's
"none should be privileged universally" as a single pair of theorems about one
key.

⚠ The domain restriction is not decoration: an ill-formed world has **no**
delivery futures at all, so its residual is empty while a wellformed world's is
a singleton. This is `WorldFuture.renderW_not_canonical`'s carrier junk showing
up again, in the key vocabulary. -/
theorem epoch_sufficient_on_wellformed {α : Type uA} :
    SufficientKeyOn (WorldFuture.Wf (α := α)) (fun w => w.epoch) (fun w => w.epoch)
      WorldFuture.DeliveryFuture := by
  intro w v hw hv hk r
  have hk' : w.epoch = v.epoch := hk
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨v, WorldFuture.delivery_refl hv, ?_⟩
    show v.epoch = t.epoch
    rw [ht.2.2]
    exact hk'.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨w, WorldFuture.delivery_refl hw, ?_⟩
    show w.epoch = t.epoch
    rw [ht.2.2]
    exact hk'

/-! ## §6. The base scope IS a scoped key.

`HistoryBase.BasedCertSound` restricts a certificate's licence to the versions a
named base reaches. In this file's vocabulary that is a **domain**, and the two
verdicts `HistoryBase.lean` proves about it are exactly a sufficiency and an
insufficiency of the *same* key on two different domains. Both are re-derived
here from §4's machinery. -/

/-- The worlds a base reaches, through a placement. -/
def reachedWorlds {α : Type uA} {V : Type uV} (B : HistoryBase.BasedWorld α V) (b : V) :
    WorldFuture.World α → Prop :=
  fun w => ∃ v, Reaches B.dag b v ∧ B.world v = w

/-- **A base-scoped certificate is sound when the key is sufficient on the
scope.** The general theorem: pin the certificate to the key of one honestly
verified world, and every version in scope that carries that key inherits the
licence. `HistoryBase.stateKeyed_sound_at_its_base` is the instance below. -/
theorem basedCertSound_of_sufficientKeyOn {α : Type uA} {V : Type uV} {K : Type u}
    (B : HistoryBase.BasedWorld α V) (b : V) (κ : WorldFuture.World α → K)
    (hsuf : SufficientKeyOn (reachedWorlds B b) κ (WorldFuture.renderW (α := α))
      WorldFuture.DeliveryFuture)
    (hwf : ∀ w, reachedWorlds B b w → WorldFuture.Wf w)
    {C : HistoryBase.VersionCert V} {w₀ : WorldFuture.World α}
    (h₀ : reachedWorlds B b w₀)
    (hst : Evidence.FreeTermination WorldFuture.DeliveryFuture
      (WorldFuture.renderW (α := α)) w₀)
    (hacc : ∀ v, C v → κ (B.world v) = κ w₀) :
    HistoryBase.BasedCertSound B b C := by
  intro v hCv hreach
  have hD : reachedWorlds B b (B.world v) := ⟨v, hreach, rfl⟩
  exact key_licenses_reuse_on hsuf h₀ hD (hacc v hCv).symm
    (WorldFuture.delivery_refl (hwf _ hD)) hst

/-- The scope of the named base is a singleton: `quiesced` is a leaf of the
placed version graph. -/
theorem reachedWorlds_quiesced (w : WorldFuture.World Holes.Val) :
    reachedWorlds HistoryBase.wBased .quiesced w ↔ w = WorldFuture.wQuiesced := by
  constructor
  · rintro ⟨v, hr, rfl⟩
    have hv : HistoryBase.WVer.quiesced = v :=
      HistoryBase.reaches_of_leaf HistoryBase.wDag_quiesced_is_a_leaf hr
    rw [← hv]
    rfl
  · rintro rfl
    exact ⟨.quiesced, Reaches.refl _ _, rfl⟩

/-- ⚠ **WITNESS FOUR: the named base's scope makes the state key sufficient.**
Within the scope the state key glues nothing, because there is only one world
in it. -/
theorem base_scope_sufficient :
    SufficientKeyOn (reachedWorlds HistoryBase.wBased .quiesced)
      (WorldFuture.observe (α := Holes.Val)) WorldFuture.renderW
      WorldFuture.DeliveryFuture := by
  intro w v hw hv _
  rw [(reachedWorlds_quiesced w).mp hw, (reachedWorlds_quiesced v).mp hv]
  exact residualEq_refl _ _ _

/-- ⚠ **WITNESS THREE: the history root's scope does NOT.** The root reaches
both `quiesced` and `pending`, whose worlds share an observation and differ in
residual — so the same key is insufficient one scope up. Which base you name
decides whether the licence holds, and this is the arithmetic of that. -/
theorem root_scope_not_sufficient :
    ¬ SufficientKeyOn (reachedWorlds HistoryBase.wBased .start)
        (WorldFuture.observe (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture := by
  intro h
  exact residual_separates_quiesced_pending
    (h WorldFuture.wQuiesced WorldFuture.wPending
      ⟨.quiesced, HistoryBase.dag_ancestry_is_not_delivery.1, rfl⟩
      ⟨.pending, HistoryBase.dag_ancestry_is_not_delivery.2.1, rfl⟩
      WorldFuture.same_observation)

/-- **`HistoryBase.stateKeyed_sound_at_its_base`, re-derived from the
abstraction.** Not restated: obtained by handing `basedCertSound_of_
sufficientKeyOn` the scope's sufficiency, the verification `WorldFuture.
stable_at_wQuiesced`, and the observation that `stateKeyed` accepts exactly the
worlds carrying `wQuiesced`'s key. -/
theorem stateKeyed_sound_at_its_base_via_keys :
    HistoryBase.BasedCertSound HistoryBase.wBased .quiesced HistoryBase.stateKeyed := by
  refine basedCertSound_of_sufficientKeyOn HistoryBase.wBased .quiesced
    WorldFuture.observe base_scope_sufficient (fun w hw => ?_)
    (w₀ := WorldFuture.wQuiesced) ⟨.quiesced, Reaches.refl _ _, rfl⟩
    WorldFuture.stable_at_wQuiesced (fun _ hv => hv)
  rw [(reachedWorlds_quiesced w).mp hw]
  exact WorldFuture.wf_of_quiesced WorldFuture.quiesced_wQuiesced

/-- **The four witnesses, together.** Insufficient: frontier-plus-epoch, and the
history root's scope. Sufficient: the observation-with-pool, and the named
base's scope. Both directions of codex's request, on the objects the two earlier
files already own. -/
theorem the_four_witnesses :
    ¬ SufficientKey (frontierEpochKey (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ SufficientKey (deliveryKey (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ ¬ SufficientKeyOn (reachedWorlds HistoryBase.wBased .start)
        (WorldFuture.observe (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ SufficientKeyOn (reachedWorlds HistoryBase.wBased .quiesced)
        (WorldFuture.observe (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture :=
  ⟨frontierEpoch_not_sufficient, deliveryKey_sufficient_render,
   root_scope_not_sufficient, base_scope_sufficient⟩

/-! ## §7. The `MinimalSummary` identification, checked.

Codex says this is `MinimalSummary` lifted from merge contexts to future
contexts. §7 checks it. The shape is the same — both are the kernel of an
observation, and that is where the universal property comes from at both indices
— and the *observations differ*, strictly, in two ways that are refutations
rather than omissions. -/

/-- **The one shape.** A key is sufficient *for an observation* when equal keys
force equal observations. Both this file's notion and `MinimalSummary`'s are
instances, and the universal property — "the observation is its own coarsest
sufficient key" — is the identity function at this generality. That is exactly
how much the universal property is worth. -/
def SufficientFor {W : Type u} {O : Type v} {K : Type w}
    (κ : W → K) (obs : W → O) : Prop :=
  ∀ w v, κ w = κ v → obs w = obs v

/-- The observation is sufficient for itself. -/
theorem sufficientFor_self {W : Type u} {O : Type v} (obs : W → O) : SufficientFor obs obs :=
  fun _ _ h => h

/-- **This file's notion is `SufficientFor` at the residual.** -/
theorem sufficientKey_iff_sufficientFor {W : Type u} {K : Type v} {R : Type w}
    (κ : W → K) (e : W → R) (F : W → W → Prop) :
    SufficientKey κ e F ↔ SufficientFor κ (Residual e F) := by
  constructor
  · intro h w v hk
    exact (residualEq_iff_eq e F w v).mp (h w v hk)
  · intro h w v hk
    exact (residualEq_iff_eq e F w v).mpr (h w v hk)

/-- The merge-context future: `t` is a future of `x` when some peer's state
merged into `x`. -/
def MergeFuture {S : Type u} [MergeState S] : S → S → Prop :=
  fun x t => ∃ z : S, t = x ⊔ z

/-- `MinimalSummary`'s observation: the context-**indexed** answer function. -/
def ctxObs {S : Type u} {R : Type v} [MergeState S] (f : S → R) (x : S) : S → R :=
  fun z => f (x ⊔ z)

/-- **`MinimalSummary.Sufficient` is `SufficientFor` at the indexed
observation** — the same shape, `ctxEquiv_iff_contexts` plus `funext`. -/
theorem sufficient_iff_sufficientFor {S : Type u} {T : Type v} {R : Type w}
    [MergeState S] (g : S → T)
    (f : S → R) : Sufficient g f ↔ SufficientFor g (ctxObs f) := by
  constructor
  · intro h x y hg
    funext z
    exact (h x y hg).2 z
  · intro h x y hg
    exact ctxEquiv_of_contexts (fun z => congrFun (h x y hg) z)

/-- ⚠ **…and a residual is only the IMAGE of that observation.** The context is
forgotten; only the set of answers survives. Everything that separates the two
constructions is this one collapse. -/
theorem residual_mergeFuture_image {S : Type u} {R : Type v}
    [MergeState S] (f : S → R) (x : S)
    (r : R) : Residual f MergeFuture x r ↔ ∃ z, ctxObs f x z = r := by
  constructor
  · rintro ⟨t, ⟨z, rfl⟩, hr⟩
    exact ⟨z, hr⟩
  · rintro ⟨z, hz⟩
    exact ⟨x ⊔ z, ⟨z, rfl⟩, hz⟩

/-- Contextual equivalence implies residual equality — the image of equal
functions is equal. So every `MinimalSummary`-sufficient summary is a
future-sufficient key at the merge index. -/
theorem residualEq_of_ctxEquiv {S : Type u} {R : Type v}
    [MergeState S] {f : S → R} {x y : S}
    (h : CtxEquiv f x y) : ResidualEq f MergeFuture x y := by
  intro r
  constructor
  · rintro ⟨t, ⟨z, rfl⟩, rfl⟩
    exact ⟨y ⊔ z, ⟨z, rfl⟩, (h.2 z).symm⟩
  · rintro ⟨t, ⟨z, rfl⟩, rfl⟩
    exact ⟨x ⊔ z, ⟨z, rfl⟩, h.2 z⟩

/-- **A sufficient summary is a sufficient key** — the containment, in one
direction only. -/
theorem sufficientKey_of_sufficient {S : Type u} {T : Type v} {R : Type w}
    [MergeState S] {g : S → T}
    {f : S → R} (h : Sufficient g f) : SufficientKey g f MergeFuture :=
  fun x y hg => residualEq_of_ctxEquiv (h x y hg)

/-! ### §7.1 The collapse is strict, at `MinimalSummary`'s own pole

`JoinHom.sawA` and `JoinHom.sawB` — the two replicas that report the same count
and are separated by a context. Swapping the two-element universe carries one to
the other, so their residuals are **equal**; `MinimalSummary.answerEq_not_
ctxEquiv` says they are not contextually equivalent. -/

/-- The involution of the two-element universe. -/
def swapBool (s : GSet Bool) : GSet Bool := fun b => s (!b)

theorem swapBool_merge (x z : GSet Bool) :
    swapBool (x ⊔ z) = swapBool x ⊔ swapBool z := rfl

theorem card_swapBool (s : GSet Bool) :
    JoinHom.card (swapBool s) = JoinHom.card s := by
  show JoinHom.bit (s true) + JoinHom.bit (s false)
    = JoinHom.bit (s false) + JoinHom.bit (s true)
  exact Nat.add_comm _ _

theorem swapBool_sawA : swapBool JoinHom.sawA = JoinHom.sawB := by
  funext b
  cases b <;> rfl

theorem swapBool_sawB : swapBool JoinHom.sawB = JoinHom.sawA := by
  funext b
  cases b <;> rfl

/-- **The two replicas have equal residuals for the exact count.** Every context
`z` for one is answered by `swapBool z` for the other. -/
theorem residualEq_sawA_sawB :
    ResidualEq JoinHom.card MergeFuture JoinHom.sawA JoinHom.sawB := by
  intro r
  constructor
  · rintro ⟨t, ⟨z, rfl⟩, rfl⟩
    refine ⟨JoinHom.sawB ⊔ swapBool z, ⟨swapBool z, rfl⟩, ?_⟩
    rw [← swapBool_sawA, ← swapBool_merge, card_swapBool]
  · rintro ⟨t, ⟨z, rfl⟩, rfl⟩
    refine ⟨JoinHom.sawA ⊔ swapBool z, ⟨swapBool z, rfl⟩, ?_⟩
    rw [← swapBool_sawB, ← swapBool_merge, card_swapBool]

/-- ⚠ **THE COLLAPSE IS STRICT.** Equal residuals, and not contextually
equivalent. So the future-context construction is **not** `MinimalSummary`'s
construction at another index: it is a strictly coarser relation, because it
observes only the image of the context map. -/
theorem residual_key_is_strictly_coarser_than_ctxEquiv :
    ResidualEq JoinHom.card MergeFuture JoinHom.sawA JoinHom.sawB
      ∧ ¬ CtxEquiv JoinHom.card JoinHom.sawA JoinHom.sawB :=
  ⟨residualEq_sawA_sawB, MinimalSummary.answerEq_not_ctxEquiv.2⟩

/-- ⚠ **…and the residual key is not a sufficient summary at all.** It glues
`sawA` to `sawB`, and `MinimalSummary.card_sufficient_injective` says every
sufficient summary for the count is injective. A receiver holding the residual
class can say whether the answer will move; it cannot say what the answer will
be. -/
theorem residual_key_not_a_sufficient_summary :
    ¬ Sufficient (resKey JoinHom.card MergeFuture) JoinHom.card := by
  intro hs
  have hbad : JoinHom.sawA = JoinHom.sawB :=
    MinimalSummary.card_sufficient_injective _ hs _ _
      (Quotient.sound residualEq_sawA_sawB)
  exact absurd (congrFun hbad false) (by decide)

/-! ### §7.2 The load-bearing lemma has no analogue

`MinimalSummary.ctxEquiv_join` is what makes `CtxQuot` a `MergeState` and
`ctxMk` a `JoinHom` — "sufficiency and mergeability never trade off". The
corresponding statement for residuals is **false**. -/

/-- The top of the two-element G-Set absorbs everything. -/
theorem gsetBool_top_merge (z : GSet Bool) :
    (fun _ => true : GSet Bool) ⊔ z = (fun _ => true) := by
  funext b
  rfl

theorem sawB_merge_sawA : JoinHom.sawB ⊔ JoinHom.sawA = (fun _ => true) := by
  funext b
  cases b <;> rfl

/-- ⚠ **RESIDUAL EQUALITY IS NOT A JOIN CONGRUENCE.** `sawA` and `sawB` have
equal residuals; merging `sawA` into both separates them, because one side
reaches the full set (count `2`, and no context can lower it) while the other
stays a singleton (count `1`).

So `ResQuot` carries **no** merge, the class map is no join homomorphism, and
`MinimalSummary`'s §1.1 — the reason its quotient is a lattice — has no analogue
at the future index. This is the sharpest sense in which the two constructions
are not the same one. -/
theorem residual_is_not_a_join_congruence :
    ResidualEq JoinHom.card MergeFuture JoinHom.sawA JoinHom.sawB
      ∧ ¬ ResidualEq JoinHom.card MergeFuture (JoinHom.sawA ⊔ JoinHom.sawA)
            (JoinHom.sawB ⊔ JoinHom.sawA) := by
  refine ⟨residualEq_sawA_sawB, fun h => ?_⟩
  have h1 : Residual JoinHom.card MergeFuture (JoinHom.sawA ⊔ JoinHom.sawA) 1 :=
    ⟨(JoinHom.sawA ⊔ JoinHom.sawA) ⊔ JoinHom.sawA, ⟨JoinHom.sawA, rfl⟩, by decide⟩
  obtain ⟨t, ⟨z, hz⟩, hc⟩ := (h 1).mp h1
  rw [sawB_merge_sawA, gsetBool_top_merge] at hz
  subst hz
  exact absurd hc (by decide)

/-- **THE VERDICT ON CODEX'S IDENTIFICATION.** Same shape: both notions are
kernels of an observation, and the universal property is that kernel
factorisation at either index. Not the same construction: the residual is the
*image* of `MinimalSummary`'s observation, the image collapse is strict at its
own pole, the residual key is not a sufficient summary, and the congruence that
makes `CtxQuot` a lattice is false for residuals.

⟨TERMINAL⟩ for the refutations; the positive reading — each construction is the
right one for its own question, stability against recomputation — is a reading
of these theorems and not itself a theorem. -/
theorem the_minimalsummary_connection :
    (∀ g : GSet Bool → Bool,
        Sufficient g JoinHom.card ↔ SufficientFor g (ctxObs JoinHom.card))
      ∧ (∀ g : GSet Bool → Bool, SufficientKey g JoinHom.card MergeFuture
          ↔ SufficientFor g (Residual JoinHom.card MergeFuture))
      ∧ (∀ (x : GSet Bool) (r : Nat),
          Residual JoinHom.card MergeFuture x r ↔ ∃ z, ctxObs JoinHom.card x z = r)
      ∧ (ResidualEq JoinHom.card MergeFuture JoinHom.sawA JoinHom.sawB
          ∧ ¬ CtxEquiv JoinHom.card JoinHom.sawA JoinHom.sawB)
      ∧ ¬ Sufficient (resKey JoinHom.card MergeFuture) JoinHom.card
      ∧ ¬ ResidualEq JoinHom.card MergeFuture (JoinHom.sawA ⊔ JoinHom.sawA)
            (JoinHom.sawB ⊔ JoinHom.sawA) :=
  ⟨fun g => sufficient_iff_sufficientFor g JoinHom.card,
   fun g => sufficientKey_iff_sufficientFor g JoinHom.card MergeFuture,
   residual_mergeFuture_image JoinHom.card,
   residual_key_is_strictly_coarser_than_ctxEquiv,
   residual_key_not_a_sufficient_summary,
   residual_is_not_a_join_congruence.2⟩

/-! ## §8. The table — which of the tree's notions are keys, and for what.

Two columns, and they are different jobs: a **key** licenses reuse, a
**certificate** licenses the stop. §8.1 collects the key verdicts, §8.2 the
certificate verdicts, and §8.3 proves the two columns are independent. -/

/-! ### §8.1 Keys -/

/-- Quiescence, read as a key. -/
def quiescedKey {α : Type uA} (w : WorldFuture.World α) : Prop := WorldFuture.Quiesced w

/-- Closure of the observation, read as a key. -/
def closedKey {α : Type uA} (w : WorldFuture.World α) : Prop :=
  Evidence.Closed (WorldFuture.observe w)

/-- Both quiesced worlds carry the same quiescence key. -/
theorem quiescedKey_glues_the_quiesced :
    quiescedKey WorldFuture.wQuiesced = quiescedKey WorldFuture.wDelivered :=
  propext ⟨fun _ => quiesced_wDelivered, fun _ => WorldFuture.quiesced_wQuiesced⟩

/-- ⚠ **Quiescence is not a sufficient key.** It is a sound *certificate*
(`WorldFuture.quiescence_is_a_sound_certificate`) and it names nothing: two
quiesced worlds have different residuals, so no verification may travel by
quiescence alone. -/
theorem quiesced_not_sufficient :
    ¬ SufficientKey (quiescedKey (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture :=
  not_sufficient_of_glues_quiesced_delivered _ quiescedKey_glues_the_quiesced

/-- ⚠ **`Evidence.Closed` is not a sufficient key either** — the witness pair
observes one state, so it carries one closure verdict, and its residuals
differ. -/
theorem closed_not_sufficient :
    ¬ SufficientKey (closedKey (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture :=
  not_sufficient_of_glues_witness_pair _ rfl

/-- **The key column.** Insufficient for the rendered view under delivery: the
state, frontier-plus-epoch, the pool alone, the epoch alone, quiescence,
closure. Sufficient: the observation-with-pool, and the world itself. -/
theorem the_key_table :
    ¬ SufficientKey (WorldFuture.observe (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ ¬ SufficientKey (frontierEpochKey (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ ¬ SufficientKey (WorldFuture.pool (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ ¬ SufficientKey (fun w : WorldFuture.World Holes.Val => w.epoch)
        WorldFuture.renderW WorldFuture.DeliveryFuture
      ∧ ¬ SufficientKey (quiescedKey (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ ¬ SufficientKey (closedKey (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ SufficientKey (deliveryKey (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ SufficientKey (fun w : WorldFuture.World Holes.Val => w) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ SufficientKeyOn (WorldFuture.Wf (α := Holes.Val))
        (fun w => w.epoch) (fun w => w.epoch) WorldFuture.DeliveryFuture :=
  ⟨observe_not_sufficient, frontierEpoch_not_sufficient, pool_not_sufficient,
   epoch_not_sufficient, quiesced_not_sufficient, closed_not_sufficient,
   deliveryKey_sufficient_render,
   sufficientKey_of_injective _ _ _ (fun _ _ h => h),
   epoch_sufficient_on_wellformed⟩

/-! ### §8.2 Certificates -/

/-- **`Evidence.Closed` licenses the VALUE evaluator under delivery.**
`Evidence.closed_freezes` is the whole proof: a closed evidence's candidate set
cannot move, so the values cannot. -/
theorem closed_licenses_the_values {α : Type uA} {w : WorldFuture.World α}
    (h : Evidence.Closed (WorldFuture.observe w)) :
    Evidence.FreeTermination WorldFuture.DeliveryFuture
      (fun u => Evidence.values (WorldFuture.observe u)) w := by
  intro v hv
  exact Evidence.values_congr (Evidence.closed_freezes h hv.1.1 hv.1.2.2)

/-- The roster-unknown world hears about `bob` — a **delivery**, since the
roster is part of the pool. -/
theorem delivery_rosterUnknown_quiesced :
    WorldFuture.DeliveryFuture WorldFuture.wRosterUnknown WorldFuture.wQuiesced :=
  ⟨⟨Evidence.exactW_extends_to_openW.1, leq_refl _,
    Evidence.exactW_extends_to_openW.2⟩, rfl, rfl⟩

/-- ⚠ **…and it does NOT license the rendered view.** `wRosterUnknown` holds a
closed evidence and renders `exact 47`; one delivery later — the arrival of a
roster member it had never heard of — it renders `provisional 47`. The report
was retracted **under delivery**, which is the future that was supposed to
contain no news.

This is `Evidence.render_retracts_when_a_new_source_appears` at the delivery
index rather than the extension index, and it is why `WorldFuture.RosterKnown`
exists. `closed_and_rosterKnown_licenses_render` immediately below proves that
the conjunction is the positive repair. -/
theorem closed_is_not_a_sound_delivery_certificate :
    ¬ WorldFuture.WorldCertSound (closedKey (α := Holes.Val)) := by
  intro h
  have hmov := h WorldFuture.wRosterUnknown Evidence.closed_exactW
    WorldFuture.wQuiesced delivery_rosterUnknown_quiesced
  rw [renderW_wQuiesced,
    show WorldFuture.renderW WorldFuture.wRosterUnknown = Evidence.View.exact 47 from
      Evidence.four_states_inhabited.1] at hmov
  exact absurd hmov (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

/-- **Closure plus a known roster licenses the rendered view under delivery.**
Closure freezes the candidate values. `RosterKnown` supplies the missing
membership-closure fact: because a delivery keeps the pool fixed, every future
roster is the present roster, so the delivery projects to an
`Evidence.SealedFuture`. Closure therefore survives as well, and
`Evidence.render_congr` says those are exactly the two facts the view reads.

The conjunction is sharp at the named boundary: closure alone is refuted by
`closed_is_not_a_sound_delivery_certificate`. -/
theorem closed_and_rosterKnown_licenses_render {α : Type uA}
    {w : WorldFuture.World α}
    (hc : Evidence.Closed (WorldFuture.observe w))
    (hr : WorldFuture.RosterKnown w) :
    Evidence.FreeTermination WorldFuture.DeliveryFuture
      (WorldFuture.renderW (α := α)) w := by
  intro v hv
  have hroster : v.roster ⊑ w.roster := by
    have heq : v.roster = w.roster :=
      congrArg (fun p => p.2.1) hv.2.1
    rw [heq]
    exact leq_refl _
  have hsealed : Evidence.SealedFuture (WorldFuture.observe w)
      (WorldFuture.observe v) :=
    WorldFuture.sealed_projects
      ⟨WorldFuture.delivery_is_extension hv, hroster, hr⟩
  obtain ⟨hvalues, hclosed⟩ := Evidence.sealed_future_of_closed hc hsealed
  exact Evidence.render_congr hvalues ⟨fun _ => hc, fun _ => hclosed⟩

/-- Values are monotone in the evidence order — the missing half of the `Stable`
bridge below. -/
theorem values_mono {α : Type uA} {s t : Evidence.ResultEvidence α} (h : s ⊑ t) :
    Evidence.values s ⊑ Evidence.values t := by
  refine (Holes.gset_leq_iff_subset _ _).mpr (fun a ha => ?_)
  obtain ⟨o, ho⟩ := (Evidence.mem_values s a).mp ha
  exact (Evidence.mem_values t a).mpr ⟨o, Evidence.candidates_grow h ho⟩

/-- What may still arrive at a world, as a `Holes.Arriving` predicate. -/
noncomputable def arriving {α : Type uA} (w : WorldFuture.World α) :
    Holes.Partial α → Prop :=
  fun Q => ∃ v, WorldFuture.DeliveryFuture w v ∧ Q = Evidence.values (WorldFuture.observe v)

/-- **`Holes.Stable` at the delivery instance IS free termination of the value
evaluator.** `Holes.lean` §6 left `Arriving` abstract and named the transport
from a real closure as unbuilt; this discharges it for *one* concrete
`Arriving` — the deliveries of a world — by an iff rather than an implication.
⟨DONE downstream in `Uwueave.EraCertificate`⟩
`era_cut_licenses_the_collapse` instantiates `Holes.Stable` at the Era delivery
cut and `era_seal_survives` transports the resulting seal;
`tests/DebtClosures/U_0012.lean` packages both with this iff. -/
theorem stable_iff_freeTermination_values {α : Type uA} (w : WorldFuture.World α) :
    Holes.Stable (arriving w) (Evidence.values (WorldFuture.observe w))
      ↔ Evidence.FreeTermination WorldFuture.DeliveryFuture
          (fun u => Evidence.values (WorldFuture.observe u)) w := by
  constructor
  · intro h v hv
    have hle : Evidence.values (WorldFuture.observe v)
        ⊑ Evidence.values (WorldFuture.observe w) := by
      show _ ⊔ _ = _
      rw [merge_comm]
      exact h _ ⟨v, hv, rfl⟩
    show Evidence.values (WorldFuture.observe v) = Evidence.values (WorldFuture.observe w)
    exact leq_antisymm hle (values_mono hv.1.1)
  · intro h Q hQ
    obtain ⟨v, hv, rfl⟩ := hQ
    have hvw : Evidence.values (WorldFuture.observe v)
        = Evidence.values (WorldFuture.observe w) := h v hv
    rw [hvw]
    exact merge_idem _

/-- **The certificate column.** Quiescence is sound. Closure is sound for the
values and **unsound** for the view. `Holes.Stable`, at the delivery instance, is
the same property as free termination of the value evaluator. -/
theorem the_certificate_table :
    WorldFuture.WorldCertSound (quiescedKey (α := Holes.Val))
      ∧ (∀ w : WorldFuture.World Holes.Val, closedKey w →
          Evidence.FreeTermination WorldFuture.DeliveryFuture
            (fun u => Evidence.values (WorldFuture.observe u)) w)
      ∧ ¬ WorldFuture.WorldCertSound (closedKey (α := Holes.Val))
      ∧ (∀ w : WorldFuture.World Holes.Val,
          Holes.Stable (arriving w) (Evidence.values (WorldFuture.observe w))
            ↔ Evidence.FreeTermination WorldFuture.DeliveryFuture
                (fun u => Evidence.values (WorldFuture.observe u)) w) :=
  ⟨WorldFuture.quiescence_is_a_sound_certificate,
   fun _ h => closed_licenses_the_values h,
   closed_is_not_a_sound_delivery_certificate,
   stable_iff_freeTermination_values⟩

/-! ### §8.3 The two columns are independent -/

/-- ⚠ **A sound certificate need not be a sufficient key.** Quiescence licenses
the stop and names nothing: a replica cannot hand its quiescence to another
replica and have it mean anything there. -/
theorem sound_certificate_need_not_be_a_sufficient_key :
    WorldFuture.WorldCertSound (quiescedKey (α := Holes.Val))
      ∧ ¬ SufficientKey (quiescedKey (α := Holes.Val)) WorldFuture.renderW
          WorldFuture.DeliveryFuture :=
  ⟨WorldFuture.quiescence_is_a_sound_certificate, quiesced_not_sufficient⟩

/-- ⚠ **…and a sufficient key licenses nothing on its own.** The world itself is
the finest key there is, and the certificate that accepts every world under it
is unsound. A key transports a verification; it is not one. -/
theorem sufficient_key_need_not_license :
    SufficientKey (fun w : WorldFuture.World Holes.Val => w) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ ¬ KeyCertSound (fun w : WorldFuture.World Holes.Val => w) WorldFuture.renderW
          WorldFuture.DeliveryFuture (fun _ => True) :=
  ⟨sufficientKey_of_injective _ _ _ (fun _ _ h => h),
   fun h => WorldFuture.not_stable_at_wPending (h WorldFuture.wPending trivial)⟩

/-- **Quiescence factors through the delivery key** — so the sound certificate
this library actually has *is* reusable, filed under the sufficient key of §5.2
and under nothing coarser. Together with `no_sound_state_cert_accepts_openW_via_
keys`: keyed by `(observe, pool)` the verification travels; keyed by `observe`
alone it is prohibited from ever being made. -/
theorem quiesced_factors_through_the_delivery_key {α : Type uA}
    (w v : WorldFuture.World α) (h : deliveryKey w = deliveryKey v) :
    WorldFuture.Quiesced w ↔ WorldFuture.Quiesced v := by
  have hobs : WorldFuture.observe w = WorldFuture.observe v := congrArg Prod.fst h
  have hpool : WorldFuture.pool w = WorldFuture.pool v := congrArg Prod.snd h
  show WorldFuture.observe w = WorldFuture.pool w ↔ WorldFuture.observe v = WorldFuture.pool v
  rw [hobs, hpool]

/-- **THE CONTACT ZONE.** The abstraction, its two verdicts on the same
certificate, and the two files it was extracted from, in one statement: the
state key is prohibited from accepting `openW`; the delivery key is sufficient
and the sound certificate we have is invariant under it; the named base's scope
rescues the state key and the root's scope does not. -/
theorem the_certificate_scope :
    (∀ C : WorldFuture.StateCert Holes.Val, WorldFuture.StateCertSound C →
        ¬ C Evidence.openW)
      ∧ SufficientKey (deliveryKey (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture
      ∧ (∀ w v : WorldFuture.World Holes.Val, deliveryKey w = deliveryKey v →
          (WorldFuture.Quiesced w ↔ WorldFuture.Quiesced v))
      ∧ HistoryBase.BasedCertSound HistoryBase.wBased .quiesced HistoryBase.stateKeyed
      ∧ ¬ SufficientKeyOn (reachedWorlds HistoryBase.wBased .start)
        (WorldFuture.observe (α := Holes.Val)) WorldFuture.renderW
        WorldFuture.DeliveryFuture :=
  ⟨fun C hC => no_sound_state_cert_accepts_openW_via_keys C hC,
   deliveryKey_sufficient_render, quiesced_factors_through_the_delivery_key,
   stateKeyed_sound_at_its_base_via_keys, root_scope_not_sufficient⟩

end Uwueave.CertificateScope
