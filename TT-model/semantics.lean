import «TT-model».syntactics
import «TT-model».reduction

open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [lc : LevelClass]

-- Interpretation interface
@[simp] def IInterp (a : Term) (P : Term → Prop) : Prop :=
  ∃ (I : Term → (Term → Prop) → Prop),
    I a P ∧ (∀ {a b}, a ⇒⋆ b → I b P → I a P)

-- Interpretations of Type types
inductive Interp (i : lc.L) (I : ∀ j, j < i → Term → Prop) : Term → (Term → Prop) → Prop where
  | pi a b Pa (Pf : Term → (Term → Prop) → Prop) :
    Interp i I a Pa →
    (∀ x, Pa x → ∃ Pb, Pf x Pb) →
    (∀ x Pb, Pf x Pb → Interp i I (subst (x +: var) b) Pb) →
    Interp i I (pi a b) (λ f ↦ ∀ x Pb, Pa x → Pf x Pb → Pb (app f x))
  | 𝒰 j (lt : j < i) : Interp i I (𝒰 j) (I j lt)
  | ℙ : Interp i I ℙ (∃ Pb, IInterp · Pb)
  | step a b P :
    a ⇒ b →
    Interp i I b P →
    Interp i I a P
notation:40 "⟦" a "⟧" i "," I "↘" P => Interp i I a P

def Interps (i : lc.L) : Term → (Term → Prop) → Prop :=
  Interp i (λ j _ a ↦ ∃ P, Interps j a P)
termination_by i

notation:40 "⟦" a "⟧" i "↘" P => Interps i a P

-- Interpretations of Prop types
inductive Interp₀ : Term → (Term → Prop) → Prop where
  | all i a b Pa (Pf : Term → (Term → Prop) → Prop) :
    Interps i a Pa →
    (∀ x, Pa x → ∃ Pb, Pf x Pb) →
    (∀ x Pb, Pf x Pb → Interp₀ (subst (x +: var) b) Pb) →
    Interp₀ (all a b) (λ f ↦ ∀ x Pb, Pa x → Pf x Pb → Pb (app f x))
  | mty : Interp₀ mty (λ _ ↦ False)
  | step a b P : a ⇒ b → Interp₀ b P → Interp₀ a P
notation:40 "⟦" a "⟧ ↘" P => Interp₀ a P

/-*------------------------
  Simple inversion lemmas
------------------------*-/

theorem interpPiInv {i I a b P} (h : ⟦ pi a b ⟧ i , I ↘ P) :
  ∃ (Pa : Term → Prop) (Pf : Term → (Term → Prop) → Prop),
    (⟦ a ⟧ i , I ↘ Pa) ∧
    (∀ x, Pa x → ∃ Pb, Pf x Pb) ∧
    (∀ x Pb, Pf x Pb → Interp i I (subst (x +: var) b) Pb) ∧
    P = (λ f ↦ ∀ x Pb, Pa x → Pf x Pb → Pb (app f x)) := by
  generalize e : pi a b = c at h
  induction h generalizing a b <;> try contradiction
  case pi Pa Pf ha hPf hb _ _ =>
    injection e with ea eb; subst ea; subst eb
    exact ⟨Pa, Pf, ha, hPf, hb, rfl⟩
  case step r _ ih =>
    subst e; cases r
    let ⟨Pa, Pf, ha, hPf, hb, e⟩ := ih rfl
    refine ⟨Pa, Pf, ?_, hPf, ?_, e⟩
    . constructor <;> assumption
    . intro x Pb PfxPb; constructor <;> apply_rules [parCong, parRefl]

theorem interp𝒰Inv {i I j P} (h : ⟦ 𝒰 j ⟧ i , I ↘ P) : ∃ lt, P = I j lt := by
  generalize e : 𝒰 j = b at h
  induction h generalizing j <;> try contradiction
  case 𝒰 j lt => injection e with e; subst e; exists lt
  case step r _ ih => subst e; cases r; exact ih rfl

theorem interps𝒰Inv {i j P} (h : ⟦ 𝒰 j ⟧ i ↘ P) :
  j < i ∧ P = λ a ↦ ∃ P, ⟦ a ⟧ j ↘ P := by
  unfold Interps at h
  let ⟨lt, e⟩ := interp𝒰Inv h
  exact ⟨lt, e⟩

theorem interpℙInv {i I P} (h : ⟦ ℙ ⟧ i , I ↘ P) : P = (∃ P, IInterp · P) := by
  generalize e : ℙ = a at h
  induction h <;> try contradiction
  case ℙ => rfl
  case step r _ ih => subst e; cases r; simp [ih]

theorem interpsℙInv {i P} (h : ⟦ ℙ ⟧ i ↘ P) : P = (∃ P, IInterp · P) := by
  unfold Interps at h; exact interpℙInv h

theorem interpAllInv' {a b P} (h : ⟦ all a b ⟧ ↘ P) :
  ∃ i Pa, ∃ (Pf : Term → (Term → Prop) → Prop),
    (⟦ a ⟧ i ↘ Pa) ∧
    (∀ x, Pa x → ∃ Pb, Pf x Pb) ∧
    (∀ x Pb, Pf x Pb → Interp₀ (subst (x +: var) b) Pb) ∧
    P = (λ f ↦ ∀ x Pb, Pa x → Pf x Pb → Pb (app f x)) := by
  generalize e : all a b = c at h
  induction h generalizing a b <;> try contradiction
  case all Pa Pf ha hPf hb _ =>
    injection e with ea eb; subst ea; subst eb
    exact ⟨_, Pa, Pf, ha, hPf, hb, rfl⟩
  case step r _ ih =>
    subst e; cases r
    let ⟨i, Pa, Pf, ha, hPf, hb, e⟩ := ih rfl
    refine ⟨i, Pa, Pf, ?_, hPf, ?_, e⟩
    . unfold Interps at *; constructor <;> assumption
    . intro x Pb PfxPb; constructor <;> apply_rules [parCong, parRefl]

theorem interpMtyInv {P} (h : ⟦ mty ⟧ ↘ P) : P = λ _ ↦ False := by
  generalize e : mty = a at h
  induction h <;> try contradiction
  case mty => rfl
  case step r _ ih => subst e; cases r; simp [ih]

/-*--------------------
  Better constructors
--------------------*-/

theorem interpsPi {i a b Pa P}
  (ha : ⟦ a ⟧ i ↘ Pa)
  (hb : ∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ i ↘ Pb) :
  P = (λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i ↘ Pb) → Pb (app f x)) →
  ⟦ pi a b ⟧ i ↘ P := by
  unfold Interps at *; intro e; subst e; constructor; assumption; assumption; simp

theorem interps𝒰 {i j} (lt : j < i) :
  ⟦ 𝒰 j ⟧ i ↘ (λ a ↦ ∃ P, ⟦ a ⟧ j ↘ P) := by
  unfold Interps at *; constructor; assumption

theorem interpsℙ {i} : ⟦ ℙ ⟧ i ↘ (∃ P, IInterp · P) := by
  unfold Interps; constructor

theorem interpsAll {i a b Pa P}
  (ha : ⟦ a ⟧ i ↘ Pa)
  (hb : ∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ ↘ Pb) :
  P = (λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ ↘ Pb) → Pb (app f x)) →
  ⟦ all a b ⟧ ↘ P := by
  intro e; subst e; constructor; assumption; assumption; simp

/-*------------------------------------------------
  Interpretation respects conversion wrt the type
------------------------------------------------*-/

theorem interpFwd {i I a b P} (r : a ⇒ b) (h : ⟦ a ⟧ i , I ↘ P) : ⟦ b ⟧ i , I ↘ P := by
  induction h generalizing b
  case pi iha ihb =>
    cases r; constructor
    all_goals intros; apply_rules [parCong, parRefl]
  case 𝒰 => cases r; constructor
  case ℙ => cases r; constructor
  case step r' _ ih =>
    let ⟨c, rc, rc'⟩ := diamond r r'
    constructor <;> apply_rules

theorem interpsFwd {i a b P} (r : a ⇒ b) (h : ⟦ a ⟧ i ↘ P) : ⟦ b ⟧ i ↘ P := by
  unfold Interps at *; apply_rules [interpFwd]

theorem interpFwd₀ {a b P} (r : a ⇒ b) (h : ⟦ a ⟧ ↘ P) : ⟦ b ⟧ ↘ P := by
  induction h generalizing b
  case all ihb =>
    cases r; constructor
    all_goals intros; apply_rules [interpsFwd, parCong, parRefl]
  case mty => cases r; constructor
  case step r' _ ih =>
    let ⟨c, rc, rc'⟩ := diamond r r'
    constructor <;> apply_rules

theorem interpsFwds {i a b P} (r : a ⇒⋆ b) (h : ⟦ a ⟧ i ↘ P) : ⟦ b ⟧ i ↘ P := by
  induction r generalizing P
  all_goals intros; apply_rules [interpsFwd]

theorem interpFwds₀ {a b P} (r : a ⇒⋆ b) (h : ⟦ a ⟧ ↘ P) : ⟦ b ⟧ ↘ P := by
  induction r generalizing P
  all_goals intros; apply_rules [interpFwd₀]

theorem interpsBwd {i a b P} (r : a ⇒ b) (h : ⟦ b ⟧ i ↘ P) : ⟦ a ⟧ i ↘ P := by
  unfold Interps at *; constructor <;> assumption

theorem interpsBwds {i a b P} (r : a ⇒⋆ b) (h : ⟦ b ⟧ i ↘ P) : ⟦ a ⟧ i ↘ P := by
  induction r generalizing P <;> apply_rules [interpsBwd]

theorem interpBwds₀ {a b P} (r : a ⇒⋆ b) (h : ⟦ b ⟧ ↘ P) : ⟦ a ⟧ ↘ P := by
  induction r generalizing P <;> apply_rules [Interp₀.step]

theorem interpsConv {i a b P} (r : a ⇔ b) (h : ⟦ a ⟧ i ↘ P) : ⟦ b ⟧ i ↘ P :=
  let ⟨_, ra, rb⟩ := r
  interpsBwds rb (interpsFwds ra h)

theorem interpConv₀ {a b P} (r : a ⇔ b) (h : ⟦ a ⟧ ↘ P) : ⟦ b ⟧ ↘ P :=
  let ⟨_, ra, rb⟩ := r
  interpBwds₀ rb (interpFwds₀ ra h)

/-*----------------------------------------------------
  Backward preservation of interpretation predicate
  (we don't need the forward direction or conversion)
----------------------------------------------------*-/

theorem interpsBwdsP {i a x y P} (r : x ⇒⋆ y) (h : ⟦ a ⟧ i ↘ P) : P y → P x := by
  unfold Interps at h; induction h generalizing x y
  case pi ihb =>
    intro h x Pb Pax PfxPb
    exact ihb x Pb PfxPb (parsApp r (Pars.refl x)) (h x Pb Pax PfxPb)
  case 𝒰 => exact λ ⟨P, h⟩ ↦ ⟨P, interpsBwds r h⟩
  case ℙ =>
    intro ⟨P, I, hI, bwd⟩
    exact ⟨P, I, bwd r hI, bwd⟩
  case step ih => exact ih r

theorem interpBwdsP₀ {a x y P} (r : x ⇒⋆ y) (h : ⟦ a ⟧ ↘ P) : P y → P x := by
  induction h generalizing x y
  case all ihb =>
    intro h x Pb Pax PfxPb
    exact ihb x Pb PfxPb (parsApp r (Pars.refl x)) (h x Pb Pax PfxPb)
  case mty => simp
  case step ih => exact ih r

/-*--------------------------------
  Interpretations are propInterps
--------------------------------*-/

theorem interpsIInterp {i a P} (h : ⟦ a ⟧ i ↘ P) : IInterp a P :=
  ⟨λ a P ↦ ⟦ a ⟧ i ↘ P, h, interpsBwds⟩

theorem interpIInterp₀ {a P} (h : ⟦ a ⟧ ↘ P) : IInterp a P :=
  ⟨λ a P ↦ ⟦ a ⟧ ↘ P, h, interpBwds₀⟩

/-*--------------------------------
  Interpretation is deterministic
--------------------------------*-/

-- ⚠️ uses funext and propext ⚠️
theorem interpDet' {i I a P Q} (hP : ⟦ a ⟧ i , I ↘ P) (hQ : ⟦ a ⟧ i , I ↘ Q) : P = Q := by
  induction hP generalizing Q
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
  case 𝒰 => let ⟨_, e⟩ := interp𝒰Inv hQ; simp [e]
  case ℙ => simp [interpℙInv hQ]
  case step r _ ih => exact ih (interpFwd r hQ)

theorem interpsDet' {i a P Q} (hP : ⟦ a ⟧ i ↘ P) (hQ : ⟦ a ⟧ i ↘ Q) : P = Q := by
  unfold Interps at *; apply_rules [interpDet']

theorem interpsCumul {i j a P} (lt : i < j) (h : ⟦ a ⟧ i ↘ P) : ⟦ a ⟧ j ↘ P := by
  unfold Interps at h; induction h generalizing j <;> unfold Interps
  case pi iha ihb =>
    constructor
    . unfold Interps at iha; exact iha lt
    . assumption
    . intro x Pb PfxPb; unfold Interps at ihb; exact ihb x Pb PfxPb lt
  case 𝒰 k _ => constructor; apply_rules [IsTrans.trans]
  case ℙ => constructor
  case step ih => constructor; assumption; unfold Interps at ih; exact ih lt

-- ⚠️ uses trichotomy of < ⚠️
theorem interpsDet {i j a P Q} (hP : ⟦ a ⟧ i ↘ P) (hQ : ⟦ a ⟧ j ↘ Q) : P = Q := by
  rcases trichotomous (r := lc.lt.lt) i j with lt | eq | gt
  . exact interpsDet' (interpsCumul lt hP) hQ
  . rw [eq] at hP; apply interpsDet' hP hQ
  . exact interpsDet' hP (interpsCumul gt hQ)

-- ⚠️ uses funext and propext ⚠️
theorem interpDet₀ {a P Q} (hP : ⟦ a ⟧ ↘ P) (hQ : ⟦ a ⟧ ↘ Q) : P = Q := by
  induction hP generalizing Q
  case all Pa Pf ha hPf _ ihb =>
    let ⟨i, Pa', Pf', ha', hPf', hb', e⟩ := interpAllInv' hQ
    subst e; apply funext; intro f
    apply propext; constructor
    . intro h x Pb' Pax' PfxPb'
      have Pax : Pa x := by rw [interpsDet ha ha']; exact Pax'
      let ⟨Pb, PfxPb⟩ := hPf x Pax
      rw [← ihb x Pb PfxPb (hb' x Pb' PfxPb')]
      exact h x Pb Pax PfxPb
    . intro h x Pb Pax PfxPb
      have Pax' : Pa' x := by rw [interpsDet ha' ha]; exact Pax
      let ⟨Pb', PfxPb'⟩ := hPf' x Pax'
      rw [ihb x Pb PfxPb (hb' x Pb' PfxPb')]
      exact h x Pb' Pax' PfxPb'
  case mty => simp [interpMtyInv hQ]
  case step r _ ih => exact ih (interpFwd₀ r hQ)

/-*------------------------
  Better inversion lemmas
------------------------*-/

-- ⚠️ uses funext and propext ⚠️
theorem interpPiInv' {i I a b P} (h : ⟦ pi a b ⟧ i , I ↘ P) :
  ∃ Pa, (⟦ a ⟧ i , I ↘ Pa) ∧
    (∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ i , I ↘ Pb) ∧
    P = (λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i , I ↘ Pb) → Pb (app f x)) := by
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
    P = (λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i ↘ Pb) → Pb (app f x)) := by
  unfold Interps at *; exact interpPiInv' h

-- ⚠️ uses funext and propext ⚠️
theorem interpAllInv {a b P} (h : ⟦ all a b ⟧ ↘ P) :
  ∃ i Pa, (⟦ a ⟧ i ↘ Pa) ∧
    (∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ ↘ Pb) ∧
    P = (λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ ↘ Pb) → Pb (app f x)) := by
  let ⟨i, Pa, Pf, ha, hPf, hfb, e⟩ := interpAllInv' h
  refine ⟨i, Pa, ha, ?_, ?_⟩
  . intro x Pax; let ⟨Pb, PfxPb⟩ := hPf x Pax
    exact ⟨Pb, hfb x Pb PfxPb⟩
  . subst e; apply funext; intro f; apply propext; constructor
    . intro h x Pb Pax hb
      let ⟨Pb', PfxPb'⟩ := hPf x Pax
      have e : Pb = Pb' := by apply interpDet₀ hb (hfb x Pb' PfxPb')
      rw [e]; apply_rules
    . intros; apply_rules

/-*----------------
  Semantic typing
----------------*-/

open sort

def semSubst σ Γ := ∀ x a,
  (In 𝒰 x a Γ → ∃ i P, (⟦ subst σ a ⟧ i ↘ P) ∧ P (σ x)) ∧
  (In ℙ x a Γ → ∃ P, (⟦ subst σ a ⟧ ↘ P) ∧ P (σ x))
infix:40 "⊨" => semSubst

def semWt𝒰 Γ a A := ∀ σ, σ ⊨ Γ → ∃ i P, (⟦ subst σ A ⟧ i ↘ P) ∧ P (subst σ a)
notation:40 Γ:41 "⊨" a:41 "∶" A:41 => semWt𝒰 Γ a A

def semWtℙ Γ a A := ∀ σ, σ ⊨ Γ → ∃ P, (⟦ subst σ A ⟧ ↘ P) ∧ P (subst σ a)
notation:40 Γ:41 "⊨ₚ" a:41 "∶" A:41 => semWtℙ Γ a A

theorem semSubstNil σ : σ ⊨ ⬝ := by
  intros _ _; constructor
  all_goals intro mem; cases mem

theorem semSubstCons {Γ : Ctxt} {σ i a A P} :
  (⟦ subst σ A ⟧ i ↘ P) → P a →
  σ ⊨ Γ → a +: σ ⊨ Γ ∷ A := by
  intro hA ha hσ x B; constructor <;> intro mem
  . cases mem
    case here => rw [substRenamed]; exists i, P
    case there x B mem =>
      rw [substRenamed]
      let ⟨in𝒰, _⟩ := hσ x B
      exact in𝒰 mem
  . cases mem
    case there x B mem =>
      rw [substRenamed]
      let ⟨_, inℙ⟩ := hσ x B
      exact inℙ mem

theorem semSubstICons {Γ : Ctxt} {σ a A P} :
  (⟦ subst σ A ⟧ ↘ P) → P a →
  σ ⊨ Γ → a +: σ ⊨ Γ ∷ᵢ A := by
  intro hA ha hσ x B; constructor <;> intro mem
  . cases mem
    case ithere x B mem =>
      rw [substRenamed]
      let ⟨in𝒰, _⟩ := hσ x B
      exact in𝒰 mem
  . cases mem
    case ihere => rw [substRenamed]; exact ⟨P, hA, ha⟩
    case ithere x B mem =>
      rw [substRenamed]
      let ⟨_, inℙ⟩ := hσ x B
      exact inℙ mem
