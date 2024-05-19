import «TT-model».syntactics
import «TT-model».reduction

open LevelClass (L)
open Term

set_option autoImplicit false

variable [lc : LevelClass]

inductive Interp i (I : (j : L) → j < i → Term → Prop) : Term → (Term → Prop) → Prop where
  | pi a b Pa (Pf : Term → (Term → Prop) → Prop) :
    Interp i I a Pa →
    (∀ x, Pa x → ∃ Pb, Pf x Pb) →
    (∀ x Pb, Pf x Pb → Interp i I (subst (x +: var) b) Pb) →
    Interp i I (pi a b) (λ f ↦ ∀ x Pb, Pa x → Pf x Pb → Pb (app f x))
  | 𝒰 (j : L) (lt : j < i) : Interp i I (𝒰 (lof j)) (I j lt)
  | mty : Interp i I mty (λ _ ↦ False)
  | lvl k : Interp i I (lvl (lof k)) (λ a ↦ ∃ j, a ⇒⋆ lof j ∧ j < k)
  | step a b P :
    a ⇒ b →
    Interp i I b P →
    Interp i I a P
notation:40 "⟦" a "⟧" i "," I "↘" P => Interp i I a P

def Interps (i : L) : Term → (Term → Prop) → Prop :=
  Interp i (λ j _ a ↦ ∃ P, Interps j a P)
termination_by i

notation:40 "⟦" a "⟧" i "↘" P => Interps i a P

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
  case lvl => contradiction
  case step r _ ih =>
    subst e; cases r
    match ih rfl with
    | ⟨Pa, Pf, ha, hPf, hb, e⟩ =>
      refine ⟨Pa, Pf, ?_, hPf, ?_, e⟩
      . constructor <;> assumption
      . intro x Pb PfxPb; constructor
        . apply parCong; apply parRefl; assumption
        . exact hb x Pb PfxPb

theorem interp𝒰Inv {i I a P} (h : ⟦ 𝒰 a ⟧ i , I ↘ P) : ∃ j lt, a ⇒⋆ lof j ∧ P = I j lt := by
  generalize e : 𝒰 a = b at h
  revert a; induction h
  all_goals intro a e; try contradiction
  case 𝒰 j lt => injection e with e; subst e; exists j, lt, Pars.refl _
  case step r _ ih => subst e; cases r; case 𝒰 r _ =>
    match ih rfl with
    | ⟨j, lt, r, e⟩ => refine ⟨j, lt, ?_, e⟩; constructor <;> assumption

theorem interpMtyInv {i I P} (h : ⟦ mty ⟧ i , I ↘ P) : P = (λ _ ↦ False) := by
  generalize e : mty = a at h
  revert e; induction h
  all_goals intro e; try contradiction
  case mty => rfl
  case step r _ ih => subst e; cases r; simp [ih]

theorem interpLvlInv {i I a P} (h : ⟦ lvl a ⟧ i , I ↘ P) : ∃ k, a ⇒⋆ lof k ∧ P = (λ a ↦ ∃ j, a ⇒⋆ lof j ∧ j < k) := by
  generalize e : lvl a = b at h
  revert a; induction h
  all_goals intro a e; try contradiction
  case lvl k => injection e with e; subst e; exists k, Pars.refl _
  case step r _ ih => subst e; cases r; case lvl r _ =>
    match ih rfl with
    | ⟨k, r, e⟩ => refine ⟨k, ?_, e⟩; constructor <;> assumption

/-*--------------------
  Better constructors
--------------------*-/

theorem interpsPi {i a b Pa P}
  (ha : ⟦ a ⟧ i ↘ Pa)
  (hb : ∀ x, Pa x → ∃ Pb, ⟦ subst (x +: var) b ⟧ i ↘ Pb) :
  P = (λ f ↦ ∀ x Pb, Pa x → (⟦ subst (x +: var) b⟧ i ↘ Pb) → Pb (app f x)) →
  ⟦ pi a b ⟧ i ↘ P := by
  unfold Interps at *; intro e; subst e; constructor; assumption; assumption; simp

theorem interps𝒰 {i j : L} (lt : j < i) :
  ⟦ 𝒰 (lof j) ⟧ i ↘ (λ a ↦ ∃ P, ⟦ a ⟧ j ↘ P) := by
  unfold Interps at *; constructor; assumption

theorem interpsMty {i} : ⟦ mty ⟧ i ↘ (λ _ ↦ False) := by
  unfold Interps at *; constructor

theorem interpsLvl {i k} : ⟦ lvl (lof k) ⟧ i ↘ (λ a ↦ ∃ j, a ⇒⋆ lof j ∧ j < k) := by
  unfold Interps at *; constructor

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
  case 𝒰 => cases r; case 𝒰 r => cases r; constructor
  case mty => cases r; apply Interp.step <;> constructor
  case lvl => cases r; case lvl r => cases r; constructor
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
  revert x y; unfold Interps at h; induction h
  case pi ihb =>
    intro _ _ r h x Pb Pax PfxPb
    exact ihb x Pb PfxPb (parsApp r (Pars.refl x)) (h x Pb Pax PfxPb)
  case 𝒰 => exact λ r ⟨P, h⟩ ↦ ⟨P, interpsBwds r h⟩
  case mty => simp
  case lvl =>
    intro _ _ _ ⟨j, _, lt⟩
    refine ⟨j, ?_, lt⟩
    apply parsTrans <;> assumption
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
  case 𝒰 =>
    match interp𝒰Inv hQ with
    | ⟨j, _, r, e⟩ => injection (parsLofInv r) with ej; subst ej; simp [e]
  case mty => simp [interpMtyInv hQ]
  case lvl =>
    match interpLvlInv hQ with
    | ⟨k, r, e⟩ => injection (parsLofInv r) with ek; subst ek; simp [e]
  case step r _ ih => exact ih (interpFwd r hQ)

theorem interpsDet' {i a P Q} (hP : ⟦ a ⟧ i ↘ P) (hQ : ⟦ a ⟧ i ↘ Q) : P = Q := by
  unfold Interps at *; apply interpDet' <;> assumption

theorem interpsCumul {i j : L} {a P} (lt : i < j) (h : ⟦ a ⟧ i ↘ P) : ⟦ a ⟧ j ↘ P := by
  revert j; unfold Interps at h; induction h
  all_goals intro j lt; unfold Interps
  case pi iha ihb =>
    constructor
    . unfold Interps at iha; exact iha lt
    . assumption
    . intros; unfold Interps at ihb; apply ihb <;> assumption
  case 𝒰 k _ => constructor; apply IsTrans.trans <;> assumption
  case mty => constructor
  case lvl => constructor
  case step ih => constructor; assumption; unfold Interps at ih; apply ih lt

-- this is the only place we need trichotomy of <
theorem interpsDet {i j a P Q} (hP : ⟦ a ⟧ i ↘ P) (hQ : ⟦ a ⟧ j ↘ Q) : P = Q := by
  rcases IsTrichotomous.trichotomous (lt := lc.lt) i j with lt | eq | gt
  . apply interpsDet' _ hQ; apply interpsCumul lt hP
  . rw [eq] at hP; apply interpsDet' hP hQ
  . apply interpsDet' hP; apply interpsCumul gt hQ

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
  unfold Interps at *; apply interpPiInv' h

theorem interps𝒰Inv {i a P} (h : ⟦ 𝒰 a ⟧ i ↘ P) :
  ∃ j, a ⇒⋆ lof j ∧ j < i ∧ P = λ a ↦ ∃ P, ⟦ a ⟧ j ↘ P := by
  unfold Interps at h
  match interp𝒰Inv h with
  | ⟨j, lt, r, e⟩ => exact ⟨j, r, lt, e⟩

theorem interpsMtyInv {i P} (h : ⟦ mty ⟧ i ↘ P) : P = (λ _ ↦ False) := by
  unfold Interps at h; apply interpMtyInv h

theorem interpsLvlInv {i a P} (h : ⟦ lvl a ⟧ i ↘ P) : ∃ k, a ⇒⋆ lof k ∧ P = (λ a ↦ ∃ j, a ⇒⋆ lof j ∧ j < k) := by
  unfold Interps at h; apply interpLvlInv h

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
  case here => rw [substRenamed]; exists i, P
  case there B mem => rw [substRenamed]; apply hσ; assumption
