import «TT-model».syntactics
import «TT-model».reduction
import «TT-model».normal

open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [lc : LevelClass]

inductive Interp (i : lc.L) (I : ∀ j, j < i → Term → Prop) : Term → (Term → Prop) → Prop where
  | ne a : ne a → Interp i I a wne
  | pi a b Pa (Pf : Term → (Term → Prop) → Prop) :
    Interp i I a Pa →
    (∀ x, Pa x → ∃ Pb, Pf x Pb) →
    (∀ x Pb, Pf x Pb → Interp i I (subst (x +: var) b) Pb) →
    Interp i I (pi a b) (λ f ↦ ∀ x Pb, Pa x → Pf x Pb → Pb (app f x))
  | 𝒰 j (lt : j < i) : Interp i I (𝒰 (lof j)) (I j lt)
  | mty : Interp i I mty wne
  | lvl k : Interp i I (lvl (lof k)) (λ a ↦ (∃ j, a ⇒⋆ lof j ∧ j < k) ∨ wne a)
  | step a b P :
    a ⇒ b →
    Interp i I b P →
    Interp i I a P
notation:40 "⟦" a "⟧" i "," I "↘" P => Interp i I a P

def Interps (i : lc.L) : Term → (Term → Prop) → Prop :=
  Interp i (λ j _ a ↦ ∃ P, Interps j a P)
termination_by i

notation:40 "⟦" a "⟧" i "↘" P => Interps i a P

/-*------------------------
  Simple inversion lemmas
------------------------*-/

theorem interpNeInv {i I a P} (h : ⟦ a ⟧ i , I ↘ P) :
  ne a → P = wne := by
  induction h <;> intro nea
  case step r _ ih => exact ih (nePar r nea)
  all_goals first | contradiction | simp

theorem interpPiInv {i I a b P} (h : ⟦ pi a b ⟧ i , I ↘ P) :
  ∃ (Pa : Term → Prop) (Pf : Term → (Term → Prop) → Prop),
    (⟦ a ⟧ i , I ↘ Pa) ∧
    (∀ x, Pa x → ∃ Pb, Pf x Pb) ∧
    (∀ x Pb, Pf x Pb → ⟦ subst (x +: var) b ⟧ i, I ↘ Pb) ∧
    P = (λ f ↦ ∀ x Pb, Pa x → Pf x Pb → Pb (app f x)) := by
  generalize e : pi a b = c at h
  induction h generalizing a b
  case ne => subst e; contradiction
  case pi Pa Pf ha hPf hb _ _ =>
    injection e with ea eb; subst ea; subst eb
    exact ⟨Pa, Pf, ha, hPf, hb, rfl⟩
  case step r _ ih =>
    subst e; cases r
    let ⟨Pa, Pf, ha, hPf, hb, e⟩ := ih rfl
    refine ⟨Pa, Pf, ?_, hPf, ?_, e⟩
    . constructor <;> assumption
    . intro x Pb PfxPb; constructor <;> apply_rules [parCong, parRefl]
  all_goals contradiction

theorem interp𝒰Inv {i I a P} (h : ⟦ 𝒰 a ⟧ i , I ↘ P) :
  ∃ j lt, a ⇒⋆ lof j ∧ P = I j lt := by
  generalize e : 𝒰 a = b at h
  induction h generalizing a
  case ne => subst e; contradiction
  case 𝒰 j lt => injection e with e; subst e; exists j, lt, Pars.refl _
  case step r _ ih =>
    subst e; let (Par.𝒰 r₁) := r
    let ⟨j, lt, r₂, e⟩ := ih rfl
    exact ⟨j, lt, Pars.trans r₁ r₂, e⟩
  all_goals contradiction

theorem interpMtyInv {i I P} (h : ⟦ mty ⟧ i , I ↘ P) : P = wne := by
  generalize e : mty = a at h
  induction h
  case ne => subst e; contradiction
  case mty => rfl
  case step r _ ih => subst e; cases r; simp [ih]
  all_goals contradiction

theorem interpLvlInv {i I a P} (h : ⟦ lvl a ⟧ i , I ↘ P) :
  ∃ k, a ⇒⋆ lof k ∧ P = (λ a ↦ (∃ j, a ⇒⋆ lof j ∧ j < k) ∨ wne a) := by
  generalize e : lvl a = b at h
  induction h generalizing a
  case ne => subst e; contradiction
  case lvl k => injection e with e; subst e; exists k, Pars.refl _
  case step r _ ih =>
    subst e; let (Par.lvl r₁) := r
    let ⟨k, r₂, e⟩ := ih rfl
    exact ⟨k, Pars.trans r₁ r₂, e⟩
  all_goals contradiction

/-
theorem interpStepInv {i I T P} (h : ⟦ T ⟧ i , I ↘ P) :
  (∃ A B, T ⇒⋆ pi A B) ∨
  (∃ i, T ⇒⋆ 𝒰 i) ∨
  (T ⇒⋆ mty) ∨
  (∃ k, T ⇒⋆ lvl (lof k)) := by
  induction h
  case ne => sorry
  case pi => left; exact ⟨_, _, Pars.refl _⟩
  case 𝒰 => right; left; exact ⟨_, Pars.refl _⟩
  case mty => right; right; left; exact Pars.refl _
  case lvl => right; right; right; exact ⟨_, Pars.refl _⟩
  case step r₁ _ h =>
    rcases h with ⟨A, B, r₂⟩ | ⟨i, r₂⟩ | r₂ | ⟨k, r₂⟩
    . left; exact ⟨A, B, Pars.trans r₁ r₂⟩
    . right; left; exact ⟨i, Pars.trans r₁ r₂⟩
    . right; right; left; exact Pars.trans r₁ r₂
    . right; right; right; exact ⟨k, Pars.trans r₁ r₂⟩
-/

/-*--------------------
  Better constructors
--------------------*-/

theorem interpsNe {i a} (nea : ne a) : ⟦ a ⟧ i ↘ wne := by
  unfold Interps; constructor; assumption

theorem interpsPi {i a b Pa P}
  (ha : ⟦ a ⟧ i ↘ Pa)
  (hb : ∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ i ↘ Pb) :
  P = (λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i ↘ Pb) → Pb (app f x)) →
  ⟦ pi a b ⟧ i ↘ P := by
  unfold Interps at *; intro e; subst e; constructor; assumption; assumption; simp

theorem interps𝒰 {i j} (lt : j < i) :
  ⟦ 𝒰 (lof j) ⟧ i ↘ (λ a ↦ ∃ P, ⟦ a ⟧ j ↘ P) := by
  unfold Interps at *; constructor; assumption

theorem interpsMty {i} : ⟦ mty ⟧ i ↘ wne := by
  unfold Interps at *; exact Interp.mty

theorem interpsLvl {i k} : ⟦ lvl (lof k) ⟧ i ↘ (λ a ↦ (∃ j, a ⇒⋆ lof j ∧ j < k) ∨ wne a) := by
  unfold Interps at *; constructor

/-*------------------------------------------------
  Interpretation respects conversion wrt the type
------------------------------------------------*-/

theorem interpFwd {i I a b P} (r : a ⇒ b) (h : ⟦ a ⟧ i , I ↘ P) : ⟦ b ⟧ i , I ↘ P := by
  induction h generalizing b
  case pi iha ihb =>
    cases r; constructor
    all_goals intros; apply_rules [parCong, parRefl]
  case ne nea => constructor; exact nePar r nea
  case 𝒰 => cases r; case 𝒰 r => cases r; constructor
  case mty => cases r; exact Interp.mty
  case lvl => cases r; case lvl r => cases r; constructor
  case step r' _ ih =>
    let ⟨c, rc, rc'⟩ := diamond r r'
    constructor <;> apply_rules

theorem interpsFwd {i a b P} (r : a ⇒ b) (h : ⟦ a ⟧ i ↘ P) : ⟦ b ⟧ i ↘ P := by
  unfold Interps at *; apply_rules [interpFwd]

theorem interpsBwd {i a b P} (r : a ⇒ b) (h : ⟦ b ⟧ i ↘ P) : ⟦ a ⟧ i ↘ P := by
  unfold Interps at *; constructor <;> assumption

theorem interpsFwds {i a b P} (r : a ⇒⋆ b) (h : ⟦ a ⟧ i ↘ P) : ⟦ b ⟧ i ↘ P := by
  induction r generalizing P <;> apply_rules [interpsFwd]

theorem interpsBwds {i a b P} (r : a ⇒⋆ b) (h : ⟦ b ⟧ i ↘ P) : ⟦ a ⟧ i ↘ P := by
  induction r generalizing P <;> apply_rules [interpsBwd]

theorem interpsConv {i a b P} (r : a ⇔ b) (h : ⟦ a ⟧ i ↘ P) : ⟦ b ⟧ i ↘ P :=
  let ⟨_, ra, rb⟩ := r
  interpsBwds rb (interpsFwds ra h)

/-*----------------------------------------------------
  Backward preservation of interpretation predicate
  (we don't need the forward direction or conversion)
----------------------------------------------------*-/

theorem interpsBwdsP {i a x y P} (r : x ⇒⋆ y) (h : ⟦ a ⟧ i ↘ P) : P y → P x := by
  unfold Interps at h; induction h generalizing x y
  case ne => exact wnePars r
  case pi ihb =>
    intro h x Pb Pax PfxPb
    exact ihb x Pb PfxPb (parsApp r (Pars.refl x)) (h x Pb Pax PfxPb)
  case 𝒰 => exact λ ⟨P, h⟩ ↦ ⟨P, interpsBwds r h⟩
  case mty => exact wnePars r
  case lvl =>
    intro Py; rcases Py with ⟨j, r₂, lt⟩ | wney
    . exact Or.inl ⟨j, parsTrans r r₂, lt⟩
    . exact Or.inr (wnePars r wney)
  case step ih => exact ih r

/-*--------------------------------
  Interpretation is deterministic
--------------------------------*-/

-- ⚠️ uses funext and propext ⚠️
theorem interpDet' {i I a P Q} (hP : ⟦ a ⟧ i , I ↘ P) (hQ : ⟦ a ⟧ i , I ↘ Q) : P = Q := by
  induction hP generalizing Q
  case ne nea => exact symm (interpNeInv hQ nea)
  case pi Pa Pf _ hPf _ iha ihb =>
    let ⟨Pa', Pf', ha', hPf', hb', e⟩ := interpPiInv hQ
    subst e; apply funext; intro f
    apply propext; constructor
    . intro h x Pb' Pax' PfxPb'
      have Pax : Pa x := by rw [iha ha']; exact Pax'
      let ⟨Pb, PfxPb⟩ := hPf x Pax
      rw [← ihb x Pb PfxPb (hb' x Pb' PfxPb')]
      exact h x Pb Pax PfxPb
    . intro h x Pb Pax PfxPb
      have Pax' : Pa' x := by rw [← iha ha']; exact Pax
      let ⟨Pb', PfxPb'⟩ := hPf' x Pax'
      rw [ihb x Pb PfxPb (hb' x Pb' PfxPb')]
      exact h x Pb' Pax' PfxPb'
  case 𝒰 =>
    let ⟨j, _, r, e⟩ := interp𝒰Inv hQ
    injection (parsLofInv r) with ej; subst ej; simp [e]
  case mty => simp [interpMtyInv hQ]
  case lvl =>
    let ⟨k, r, e⟩ := interpLvlInv hQ
    injection (parsLofInv r) with ek; subst ek; simp [e]
  case step r _ ih => exact ih (interpFwd r hQ)

theorem interpsDet' {i a P Q} (hP : ⟦ a ⟧ i ↘ P) (hQ : ⟦ a ⟧ i ↘ Q) : P = Q := by
  unfold Interps at *; apply_rules [interpDet']

theorem interpsCumul {i j a P} (lt : i < j) (h : ⟦ a ⟧ i ↘ P) : ⟦ a ⟧ j ↘ P := by
  unfold Interps at h; induction h generalizing j <;> unfold Interps
  case ne nea => constructor; exact nea
  case pi iha ihb =>
    constructor
    . unfold Interps at iha; exact iha lt
    . assumption
    . intro x Pb PfxPb; unfold Interps at ihb; exact ihb x Pb PfxPb lt
  case 𝒰 k _ => constructor; apply_rules [IsTrans.trans]
  case mty => exact Interp.mty
  case lvl => constructor
  case step ih => constructor; assumption; unfold Interps at ih; exact ih lt

-- this is the only place we need trichotomy of <
theorem interpsDet {i j a P Q} (hP : ⟦ a ⟧ i ↘ P) (hQ : ⟦ a ⟧ j ↘ Q) : P = Q := by
  rcases trichotomous (r := lc.lt.lt) i j with lt | eq | gt
  . exact interpsDet' (interpsCumul lt hP) hQ
  . rw [eq] at hP; apply interpsDet' hP hQ
  . exact interpsDet' hP (interpsCumul gt hQ)

/-*------------------------
  Better inversion lemmas
------------------------*-/

-- ⚠️ uses funext and propext ⚠️
theorem interpPiInv' {i I a b P} (h : ⟦ pi a b ⟧ i , I ↘ P) :
  ∃ Pa, (⟦ a ⟧ i , I ↘ Pa) ∧
    (∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ i , I ↘ Pb) ∧
    P = λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i , I ↘ Pb) → Pb (app f x) := by
  let ⟨Pa, Pf, ha, hPf, hfb, e⟩ := interpPiInv h
  refine ⟨Pa, ha, ?_, ?_⟩
  . intro x Pax; let ⟨Pb, PfxPb⟩ := hPf x Pax
    exact ⟨Pb, hfb x Pb PfxPb⟩
  . subst e; apply funext; intro f; apply propext; constructor
    . intro h x Pb Pax hb
      let ⟨Pb', PfxPb'⟩ := hPf x Pax
      have e : Pb = Pb' := by apply interpDet' hb (hfb x Pb' PfxPb')
      rw [e]; apply_rules
    . intros; apply_rules

theorem interpsPiInv {i a b P} (h : ⟦ pi a b ⟧ i ↘ P) :
  ∃ Pa, (⟦ a ⟧ i ↘ Pa) ∧
    (∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ i ↘ Pb) ∧
    P = λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i ↘ Pb) → Pb (app f x) := by
  unfold Interps at *; exact interpPiInv' h

theorem interps𝒰Inv {i a P} (h : ⟦ 𝒰 a ⟧ i ↘ P) :
  ∃ j, j < i ∧ a ⇒⋆ lof j ∧ P = λ a ↦ ∃ P, ⟦ a ⟧ j ↘ P := by
  unfold Interps at h
  let ⟨j, lt, r, e⟩ := interp𝒰Inv h
  exact ⟨j, lt, r, e⟩

theorem interpsMtyInv {i P} (h : ⟦ mty ⟧ i ↘ P) : P = wne := by
  unfold Interps at h; exact interpMtyInv h

theorem interpsLvlInv {i a P} (h : ⟦ lvl a ⟧ i ↘ P) :
  ∃ k, a ⇒⋆ lof k ∧ P = (λ a ↦ (∃ j, a ⇒⋆ lof j ∧ j < k) ∨ wne a) := by
  unfold Interps at h; exact interpLvlInv h

/-
theorem interpsStepInv {I T P} (h : ⟦ T ⟧ I ↘ P) :
  (∃ A B, T ⇒⋆ pi A B) ∨
  (∃ i, T ⇒⋆ 𝒰 i) ∨
  (T ⇒⋆ mty) ∨
  (∃ k, T ⇒⋆ lvl (lof k)) := by
  unfold Interps at h; exact interpStepInv h
-/

/-*------------------------
  Reducibility candidates
------------------------*-/

@[simp]
def CR (P : Term → Prop) : Prop :=
  ∀ a, (wne a → P a) ∧ (P a → wnf a)

theorem adqWnf {i I a P}
  (adq : ∀ {a P}, (⟦ a ⟧ i , I ↘ P) → CR P)
  (h : ⟦ a ⟧ i , I ↘ P) : wnf a := by
  induction h
  case ne a nea => exact wneWnf (neWne nea)
  case 𝒰 | mty | lvl => exact nfWnf ⟨⟩
  case step r _ wnfb => exact wnfPar r wnfb
  case pi ha hPf _ wnfa wnfb =>
    let ⟨CRne, _⟩ := adq ha (var 0)
    let ⟨Pb, PfPb⟩ := hPf (var 0) (CRne (neWne ⟨⟩))
    let wnfb := wnfb (var 0) Pb PfPb
    rw [substToRename] at wnfb
    apply wnfPi wnfa (wnfRename wnfb)

theorem adequacy {i a P} (h : ⟦ a ⟧ i ↘ P) : CR P := by
  unfold Interps at h; induction h
  case ne => intro; exact ⟨id, wneWnf⟩
  case pi hPf _ iha ihb =>
    intro f; constructor
    . intro wnef x Pb Pax PfxPb
      let ⟨_, CRnf⟩ := iha x
      let ⟨CRne, _⟩ := ihb x Pb PfxPb (app f x)
      exact CRne (wneApp wnef (CRnf Pax))
    . intro h
      let ⟨CRne, _⟩ := iha (var 0)
      let Pa0 := (CRne (neWne ⟨⟩))
      let ⟨Pb, PfPb⟩ := hPf (var 0) Pa0
      let Pbf0 := h (var 0) Pb Pa0 PfPb
      let ⟨_, CRnf⟩ := ihb (var 0) Pb PfPb (app f (var 0))
      exact wnfAppInv (CRnf Pbf0)
  case 𝒰 j _ =>
    intro a; constructor
    . intro wnea
      let ⟨b, nfb, r⟩ := wnea
      exact ⟨wne, interpsBwds r (interpsNe nfb)⟩
    . intro h
      let ⟨P, ha⟩ := h
      unfold Interps at ha
      refine adqWnf (λ {a} {P} ha ↦ @adequacy j a P ?_) ha
      unfold Interps; exact ha
  case mty => intro b; exact ⟨id, wneWnf⟩
  case lvl =>
    intro _; constructor
    . exact Or.inr
    . intro Pa; rcases Pa with ⟨_, r, _⟩ | wnea
      . exact ⟨lof _, ⟨⟩, r⟩
      . exact wneWnf wnea
  case step ih => exact ih
termination_by i

/-*----------------
  Semantic typing
----------------*-/

def semSubst σ Γ := ∀ x a, In x a Γ → ∃ i P, (⟦ subst σ a ⟧ i ↘ P) ∧ P (σ x)
infix:40 "⊨" => semSubst

def semWt Γ a A := ∀ σ, σ ⊨ Γ → ∃ i P, (⟦ subst σ A ⟧ i ↘ P) ∧ P (subst σ a)
notation:40 Γ:41 "⊨" a:41 "∶" A:41 => semWt Γ a A

theorem semSubstNil σ : σ ⊨ ⬝ := by
  intro _ _ mem; cases mem

theorem semSubstCons {Γ : Ctxt} {σ i a A P} :
  (⟦ subst σ A ⟧ i ↘ P) → P a →
  σ ⊨ Γ → a +: σ ⊨ Γ ∷ A := by
  intro hA ha hσ x B mem
  cases mem
  case here => rw [substRename]; exists i, P
  case there B mem => rw [substRename]; apply_rules [hσ]
