import «TT-model».syntactics
import «TT-model».reduction

open Nat
open Term

set_option autoImplicit false

inductive Interp i (I : Nat → Term → Prop) : Term → (Term → Prop) → Prop where
  | pi a b Pa (Pf : Term → (Term → Prop) → Prop) :
    Interp i I a Pa →
    (∀ x, Pa x → ∃ Pb, Pf x Pb) →
    (∀ x Pb, Pf x Pb → Interp i I (subst (x +: var) b) Pb) →
    Interp i I (pi a b) (λ f ↦ ∀ x Pb, Pa x → Pf x Pb → Pb (app f x))
  | 𝒰 j : j < i → Interp i I (𝒰 j) (I j)
  | mty : Interp i I mty (λ _ ↦ False)
  | step a b P :
    a ⇒ b →
    Interp i I b P →
    Interp i I a P
notation:40 "⟦" a "⟧" i "," I "↘" P => Interp i I a P

def Interps (i : Nat) : Term → (Term → Prop) → Prop :=
  Interp i (λ j a ↦ if j < i then ∃ P, Interps j a P else False)
notation:40 "⟦" a "⟧" i "↘" P => Interps i a P

theorem interp𝒰 {i I j P} : P = I j → j < i → ⟦ 𝒰 j ⟧ i , I ↘ P := by
  intros e lt; subst e; constructor; assumption

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
  revert a b e; induction h <;> intro a b e
  case pi Pa Pf ha hPf hb _ _ =>
    injection e with ea eb; subst ea; subst eb
    exact ⟨Pa, Pf, ha, hPf, hb, rfl⟩
  case 𝒰 => contradiction
  case mty => contradiction
  case step r _ ih =>
    subst e; cases r
    match ih rfl with
    | ⟨Pa, Pf, ha, hPf, hb, e⟩ =>
      refine ⟨Pa, Pf, ?_, hPf, ?_, e⟩
      . constructor <;> assumption
      . intro x Pb PfxPb; constructor
        . apply parCong; apply parRefl; assumption
        . exact hb x Pb PfxPb

theorem interp𝒰Inv {i I j P} (h : ⟦ 𝒰 j ⟧ i , I ↘ P) : j < i ∧ P = I j := by
  generalize e : 𝒰 j = a at h
  revert e; induction h <;> intro e
  case pi => contradiction
  case 𝒰 lt => injection e with e; simp [lt, e]
  case mty => contradiction
  case step r _ ih => subst e; cases r; simp [ih]

theorem interpMtyInv {i I P} (h : ⟦ mty ⟧ i , I ↘ P) : P = (λ _ ↦ False) := by
  generalize e : mty = a at h
  revert e; induction h <;> intro e
  case pi => contradiction
  case 𝒰 => contradiction
  case mty => rfl
  case step r _ ih => subst e; cases r; simp [ih]

/-*--------------------------------
  Getting rid of the < in Interps
--------------------------------*-/

theorem interpLtTo {i I a P} (h : ⟦ a ⟧ i , I ↘ P) :
  ⟦ a ⟧ i , (λ j a ↦ if j < i then I j a else False) ↘ P := by
  induction h <;> try (constructor <;> assumption)
  case 𝒰 => apply interp𝒰; split <;> simp; assumption

theorem interpLtFrom {i I a P}
  (h : ⟦ a ⟧ i , (λ j a ↦ if j < i then I j a else False) ↘ P) :
  ⟦ a ⟧ i , I ↘ P := by
  induction h <;> try (constructor <;> assumption)
  case 𝒰 => apply interp𝒰; split <;> simp; assumption

-- ⚠️ uses funext and propext ⚠️
theorem interpLt i : Interps i = Interp i (λ j a ↦ ∃ P, ⟦ a ⟧ j ↘ P) := by
  apply funext; intros; apply funext; intros; apply propext; constructor
  . intro h; unfold Interps at h; apply interpLtFrom; exact h
  . intro h; unfold Interps; apply interpLtTo; exact h

/-*--------------------
  Better constructors
--------------------*-/

theorem interpPi {i I a b Pa P}
  (ha : ⟦ a ⟧ i , I ↘ Pa)
  (hb : ∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ i , I ↘ Pb) :
  P = (λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i , I ↘ Pb) → Pb (app f x)) →
  ⟦ pi a b ⟧ i , I ↘ P := by
  intro e; subst e; constructor; assumption; assumption; simp

theorem interpsPi {i a b Pa P}
  (ha : ⟦ a ⟧ i ↘ Pa)
  (hb : ∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ i ↘ Pb) :
  P = (λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i ↘ Pb) → Pb (app f x)) →
  ⟦ pi a b ⟧ i ↘ P := by
  rw [interpLt] at *; apply interpPi ha hb

theorem interps𝒰 {i j} (lt : j < i) :
  ⟦ 𝒰 j ⟧ i ↘ (λ a ↦ ∃ P, ⟦ a ⟧ j ↘ P) := by
  rw [interpLt]; apply interp𝒰 rfl lt

theorem interpsMty {i} : ⟦ mty ⟧ i ↘ (λ _ ↦ False) := by
  rw [interpLt]; constructor

/-*------------------------------------------------
  Interpretation respects conversion wrt the type
------------------------------------------------*-/

theorem interpFwd {i I a b P} (r : a ⇒ b) (h : ⟦ a ⟧ i , I ↘ P) : ⟦ b ⟧ i , I ↘ P := by
  revert b; induction h <;> intro b r
  case pi iha ihb =>
    cases r; constructor
    . apply iha; assumption
    . assumption
    . intros; apply ihb; assumption; apply parCong; apply parRefl; assumption
  case 𝒰 => cases r; constructor; assumption
  case mty => cases r; apply Interp.step <;> constructor
  case step r' _ ih =>
    match diamond r r' with
    | ⟨c, rc, rc'⟩ => constructor; exact rc; exact (ih rc')

theorem interpsFwd {i a b P} (r : a ⇒ b) (h : ⟦ a ⟧ i ↘ P) : ⟦ b ⟧ i ↘ P := by
  unfold Interps at *; apply interpFwd; exact r; assumption

theorem interpsBwd {i a b P} (r : a ⇒ b) (h : ⟦ b ⟧ i ↘ P) : ⟦ a ⟧ i ↘ P := by
  unfold Interps at *; constructor; exact r; assumption

theorem interpsFwds {i a b P} (r : a ⇒⋆ b) (h : ⟦ a ⟧ i ↘ P) : ⟦ b ⟧ i ↘ P := by
  revert P; induction r
  case refl => simp
  case trans ih => intro P h; apply ih; apply interpsFwd <;> assumption

theorem interpsBwds {i a b P} (r : a ⇒⋆ b) (h : ⟦ b ⟧ i ↘ P) : ⟦ a ⟧ i ↘ P := by
  revert P; induction r
  case refl => simp
  case trans ih => intro P h; apply interpsBwd; assumption; apply ih; assumption

theorem interpsConv {i a b P} (r : a ⇔ b) (h : ⟦ a ⟧ i ↘ P) : ⟦ b ⟧ i ↘ P :=
  match r with
  | ⟨_, ra, rb⟩ => interpsBwds rb (interpsFwds ra h)

/-*----------------------------------------------------
  Backward preservation of interpretation predicate
  (we don't need the forward direction or conversion)
----------------------------------------------------*-/

theorem interpsBwdsP {i a x y P} (r : x ⇒⋆ y) (h : ⟦ a ⟧ i ↘ P) : P y → P x := by
  revert x y; rw [interpLt] at h; induction h
  case pi ihb =>
    intro _ _ r h x Pb Pax PfxPb
    exact ihb x Pb PfxPb (parsApp r (Pars.refl x)) (h x Pb Pax PfxPb)
  case 𝒰 => exact λ r ⟨P, h⟩ ↦ ⟨P, interpsBwds r h⟩
  case mty => simp
  case step ih => exact ih

/-*--------------------------------
  Interpretation is deterministic
--------------------------------*-/

-- ⚠️ uses funext and propext ⚠️
theorem interpDet' {i I a P Q} (hP : ⟦ a ⟧ i , I ↘ P) (hQ : ⟦ a ⟧ i , I ↘ Q) : P = Q := by
  revert Q; induction hP <;> intro Q hQ
  case pi Pa Pf _ hPf _ iha ihb =>
    match interpPiInv hQ with
    | ⟨Pa', Pf', ha', hPf', hb', e⟩ =>
      subst e; apply funext; intro f
      apply propext; constructor
      . intro h x Pb' Pax' PfxPb'
        have Pax : Pa x := by rw [iha ha']; exact Pax'
        match hPf x Pax with
        | ⟨Pb, PfxPb⟩ =>
          rw [← ihb x Pb PfxPb (hb' x Pb' PfxPb')]
          exact h x Pb Pax PfxPb
      . intro h x Pb Pax PfxPb
        have Pax' : Pa' x := by rw [← iha ha']; exact Pax
        match hPf' x Pax' with
        | ⟨Pb', PfxPb'⟩ =>
          rw [ihb x Pb PfxPb (hb' x Pb' PfxPb')]
          exact h x Pb' Pax' PfxPb'
  case 𝒰 => simp [interp𝒰Inv hQ]
  case mty => simp [interpMtyInv hQ]
  case step r _ ih => exact ih (interpFwd r hQ)

theorem interpsDet' {i a P Q} (hP : ⟦ a ⟧ i ↘ P) (hQ : ⟦ a ⟧ i ↘ Q) : P = Q := by
  unfold Interps at *; apply interpDet' <;> assumption

theorem interpCumul {i j I a P} : i ≤ j → (⟦ a ⟧ i , I ↘ P) → (⟦ a ⟧ j , I ↘ P) := by
  intro lt h; revert j; induction h <;> intro j lt
  case pi iha ihb =>
    constructor
    . exact iha lt
    . assumption
    . intros; apply ihb <;> assumption
  case 𝒰 => constructor; omega
  case mty => constructor
  case step ih => constructor; assumption; apply ih lt

theorem interpsCumul {i j a P} : i ≤ j → (⟦ a ⟧ i ↘ P) → (⟦ a ⟧ j ↘ P) := by
  rw [interpLt]; rw [interpLt]; apply interpCumul

theorem interpsDet {i j a P Q} (hP : ⟦ a ⟧ i ↘ P) (hQ : ⟦ a ⟧ j ↘ Q) : P = Q := by
  if i < j then
    apply interpsDet' _ hQ
    apply interpsCumul _ hP; omega
  else
    apply interpsDet' hP
    apply interpsCumul _ hQ; omega

/-*------------------------
  Better inversion lemmas
------------------------*-/

-- ⚠️ uses funext and propext ⚠️
theorem interpPiInv' {i I a b P} (h : ⟦ pi a b ⟧ i , I ↘ P) :
  ∃ Pa, (⟦ a ⟧ i , I ↘ Pa) ∧
    (∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ i , I ↘ Pb) ∧
    P = λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i , I ↘ Pb) → Pb (app f x) := by
  match interpPiInv h with
  | ⟨Pa, Pf, ha, hPf, hfb, e⟩ =>
    refine ⟨Pa, ha, ?_, ?_⟩
    . intro x Pax; match hPf x Pax with
      | ⟨Pb, PfxPb⟩ => exact ⟨Pb, hfb x Pb PfxPb⟩
    . subst e; apply funext; intro f; apply propext; constructor
      . intro h x Pb Pax hb
        apply h x Pb Pax
        match hPf x Pax with
        | ⟨Pb', PfxPb'⟩ =>
        have e : Pb = Pb' := by apply interpDet' hb (hfb x Pb' PfxPb')
        rw [e]; exact PfxPb'
      . intro h x Pb Pax PfxPb
        apply h x Pb Pax
        apply hfb x Pb PfxPb

theorem interpsPiInv {i a b P} (h : ⟦ pi a b ⟧ i ↘ P) :
  ∃ Pa, (⟦ a ⟧ i ↘ Pa) ∧
    (∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ i ↘ Pb) ∧
    P = λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i ↘ Pb) → Pb (app f x) := by
  rw [interpLt] at *; apply interpPiInv' h

theorem interps𝒰Inv {i j P} (h : ⟦ 𝒰 j ⟧ i ↘ P) :
  j < i ∧ P = λ a ↦ ∃ P, ⟦ a ⟧ j ↘ P := by
  rw [interpLt] at h
  apply interp𝒰Inv h

theorem interpsMtyInv {i P} (h : ⟦ mty ⟧ i ↘ P) : P = (λ _ ↦ False) := by
  rw [interpLt] at h
  apply interpMtyInv h

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
  case here =>
    have e : subst (a +: σ) (rename succ A) = (subst (a +: σ) ∘ rename succ) A := by rfl
    rw [e, substRename]
    exists i, P
  case there B mem =>
    have e : subst (a +: σ) (rename succ B) = (subst (a +: σ) ∘ rename succ) B := by rfl
    rw [e, substRename]
    apply hσ <;> assumption
