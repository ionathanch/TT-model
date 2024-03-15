{-# OPTIONS --rewriting --with-K #-}

open import common
import accessibility

{-# BUILTIN REWRITE _≡_ #-}

{-----------------------------------------------------------
  This model is modelled after Conor McBride's
    Outrageous but Meaningful Coincidences (2010),
  https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf.
  It wasn't designed for modelling via CwFs,
  but it fits and I think is more nicely structured.

  The model is parametrized over well-founded levels,
  i.e. levels with a strict transitive order
  s.t. all levels are accessible.
  We also assume that that accessibility predicates
  are mere propositions (all propositionally equal),
  and for convenience mere propness computes to refl
  on definitionally equal proofs of accessibility
  (which requires --with-K).
-----------------------------------------------------------}

module model
  (Level : Set)
  (_<_ : Level → Level → Set)
  (trans< : ∀ {i j k} → i < j → j < k → i < k)
  (wf : accessibility.WF Level _<_) where
open accessibility Level _<_
open accext

funeq : ∀ {A₁ A₂ : Set} {B : A₂ → Set} (p : A₁ ≡ A₂) →
  ((a : A₂) → B a) ≡ ((a : A₁) → B (transp _ p a))
funeq refl = refl

accPropRefl : ∀ {k} (acc : Acc k) → accProp acc acc ≡ refl
accPropRefl acc with refl ← accProp acc acc = refl

-- This fails confluence checking as accProp reduces on acc<
{-# REWRITE accPropRefl #-}

{-----------------------------------------------------------
  This is the desired direct model of universes,
  which isn't valid since it fails strict positivity:
  the domain el j A could return U j if A is Û.
  However, its level must be strictly smaller,
  so the model is in fact valid,
  but we must induct on accessibility of levels
  to convince Agda of this fact.
-----------------------------------------------------------}

module direct where
  data U (k : Level) : Set
  el : ∀ k → U k → Set

  {-# NO_POSITIVITY_CHECK #-}
  data U k where
    Û : U k
    ⊥̂ : U k
    Π̂ : ∀ j → j < k → (A : U j) → (el j A → U k) → U k

  el k Û = U k
  el k ⊥̂  = ⊥
  el k (Π̂ j j<k A B) = (x : el j A) → el k (B x)

  lift : ∀ {j k} → j < k → U j → U k
  lift _ Û = Û
  lift _ ⊥̂ = ⊥̂
  lift j<k (Π̂ i i<j A B) = Π̂ i (trans< i<j j<k) A (λ a → lift j<k (B a))

  el→ : ∀ {j k} → (j<k : j < k) → ∀ u → el j u → el k (lift j<k u)
  el→ j<k Û = lift j<k
  el→ _ ⊥̂  ()
  el→ j<k (Π̂ i i<j A B) b a = el→ j<k (B a) (b a)

{-----------------------------------------------------------
  A universe of codes U' at level k, and
  an interpretation el' of codes into Agda types,
  parametrized over U, el at strictly smaller levels.
  U<, el< then instantiate the parameters of U', el'
  with themselves inductively over accessibility.
-----------------------------------------------------------}

data U' k (U< : ∀ {j} → j < k → Set) (el< : ∀ {j} (j<k : j < k) → U< j<k → Set) : Set where
  Û : U' k U< el<
  ⊥̂ : U' k U< el<
  →̂ : U' k U< el< → U' k U< el< → U' k U< el<
  Π̂ : ∀ j → (j<k : j < k) → (A : U< j<k) → (el< j<k A → U' k U< el<) → U' k U< el<

el' : ∀ k (U< : ∀ {j} → j < k → Set) (el< : ∀ {j} (j<k : j < k) → U< j<k → Set) → U' k U< el< → Set
el' k U< el< Û = U' k U< el<
el' k U< el< ⊥̂  = ⊥
el' k U< el< (→̂ A B) = el' k U< el< A → el' k U< el< B
el' k U< el< (Π̂ j j<k A B) = (a : el< j<k A) → el' k U< el< (B a)

U<  : ∀ {k} → Acc k → ∀ {j} → j < k → Set
el< : ∀ {k} (p : Acc k) {j} (j<k : j < k) → U< p j<k → Set

U<  (acc< f) {j} j<k = U'  j (U< (f j<k)) (el< (f j<k))
el< (acc< f) {j} j<k = el' j (U< (f j<k)) (el< (f j<k))

{-----------------------------------------------------------
  Universes are cumulative:
  a code in universe j can be lifted into a universe k > j
  such that the interpretation is preserved.
  We prove this in general for U' and el' over arbitrary
  proofs of accessibility of levels,
  then instantiate to the proof by well-foundedness.
  The parameters of U', el' involve accessibility proofs,
  requiring many aps on and coercions across equalities,
  especially since funext and accProp don't compute away.
-----------------------------------------------------------}

el'≡1 : ∀ {k} {acc₁ acc₂ : Acc k} (A : U' k (U< acc₁) (el< acc₁)) →
  let A' = transp (λ a → U' k (U< a) (el< a)) (accProp acc₁ acc₂) A
  in el' k (U< acc₂) (el< acc₂) A' ≡ el' k (U< acc₁) (el< acc₁) A
el'≡1 {k} {acc₁} {acc₂} A =
  cong (λ a → el' k (U< a) (el< a)
                  (transp (λ a → U' k (U< a) (el< a))
                          (accProp acc₁ a) A))
       (accProp acc₂ acc₁)

el'→1 : ∀ {k} {acc₁ acc₂ : Acc k} (A : U' k (U< acc₁) (el< acc₁)) →
  let A' = transp (λ a → U' k (U< a) (el< a)) (accProp acc₁ acc₂) A
  in el' k (U< acc₂) (el< acc₂) A' → el' k (U< acc₁) (el< acc₁) A
el'→1 A = transp (λ T → T) (el'≡1 A)

lift' : ∀ {j k} (accj : Acc j) (acck : Acc k) → j < k → U' j (U< accj) (el< accj) → U' k (U< acck) (el< acck)
lift' _ _ _ Û = Û
lift' _ _ _ ⊥̂  = ⊥̂
lift' accj acck j<k (→̂  A B) = →̂  (lift' accj acck j<k A) (lift' accj acck j<k B)
lift' accj@(acc< f) acck@(acc< g) j<k (Π̂ i i<j A B) =
  Π̂ i (trans< i<j j<k) _ (λ a → lift' accj acck j<k (B (el'→1 {i} {f i<j} {g (trans< i<j j<k)} A a)))

-- Clearly this doesn't hold for Û : U j, since el j Û ≡ U j ≢ U k ≡ el k (lift j<k Û).
el'≡ : ∀ {j k} (accj : Acc j) (acck : Acc k) (j<k : j < k) (u : U' j (U< accj) (el< accj)) →
  el' j (U< accj) (el< accj) u ≡ el' k (U< acck) (el< acck) (lift' accj acck j<k u)
el'≡ (acc< f) (acc< g) j<k Û = {!   !}
el'≡ accj acck j<k ⊥̂  = refl
el'≡ accj acck j<k (→̂  A B)
  rewrite el'≡ accj acck j<k A
  rewrite el'≡ accj acck j<k B = refl
el'≡ {j} {k} (acc< f) (acc< g) j<k (Π̂ i i<j A B) = trans p q where
  p : (∀ a → el' j _ _ (B a)) ≡ (∀ a → el' k _ _ (lift' _ _ j<k (B a)))
  p = cong (λ f → ∀ a → f a) (funext (λ a → el'≡ _ _ j<k (B a)))
  q : (∀ a → el' k _ _ (lift' _ _ j<k (B a))) ≡
      (∀ a → el' k _ _ (lift' _ _ j<k (B (el'→1 A a))))
  q = funeq (el'≡1 A)

-- This doesn't hold for A →̂  B : U j,
-- since we're given b : el j A → el j B and a : el k (lift j<k A),
-- and the argument a can't be lowered from k to j to fit into the function b.
el'→ : ∀ {j k} (accj : Acc j) (acck : Acc k) (j<k : j < k) (u : U' j (U< accj) (el< accj)) →
  el' j (U< accj) (el< accj) u → el' k (U< acck) (el< acck) (lift' accj acck j<k u)
el'→ accj acck j<k Û = lift' accj acck j<k
el'→ _ _ j<k ⊥̂  = λ b → b
el'→ (acc< f) (acc< g) j<k (→̂  A B) b a = {!   !}
el'→ accj@(acc< f) acck@(acc< g) j<k (Π̂ i i<j A B) b a =
  let a' = el'→1 A a in el'→ accj acck j<k (B a') (b a')

{-----------------------------------------------------------
  Universes, their interpretations, and cumulativity,
  instantiated over well-foundedness of levels.
-----------------------------------------------------------}

U : ∀ k → Set
U k = U' k (U< (wf k)) (el< (wf k))

el : ∀ k → U k → Set
el k = el' k (U< (wf k)) (el< (wf k))

lift : ∀ {j k} → j < k → U j → U k
lift = lift' (wf _) (wf _)

el≡ : ∀ {j k} → (j<k : j < k) → ∀ u → el j u ≡ el k (lift j<k u)
el≡ = el'≡ (wf _) (wf _)

el→ : ∀ {j k} → (j<k : j < k) → ∀ u → el j u → el k (lift j<k u)
el→ = el'→ (wf _) (wf _)

{-----------------------------------------------------------
  Inductively-defined contexts and their interpretations
  as nested dependent pairs, or "dependent lists".
  The types of semantic types and terms Ty, Tm are defined
  mutually but they don't have to be; they can come after.
-----------------------------------------------------------}

data C : Set
em : C → Set

Ty : Level → C → Set
Ty k Γ = em Γ → U k

Tm : ∀ k → (Γ : C) → Ty k Γ → Set
Tm k Γ A = (γ : em Γ) → el k (A γ)

infixl 30 _▷_
data C where
  ∙ : C
  _▷_ : ∀ {k} → (Γ : C) → Ty k Γ → C

em ∙ = ⊤
em (Γ ▷ A) = Σ[ γ ∈ em Γ ] el _ (A γ)

{-----------------------------------------------------------
  Cumulativity tells us that we are allowed to lift types
  from lower levels to higher ones,
  as well as terms to ones typed at higher levels.
  I believe terms are in fact equal to their lifts,
  but the equality types are tricky to transport,
  and we don't need that fact anyway.
-----------------------------------------------------------}

liftTy : ∀ {j k Γ} → j < k → Ty j Γ → Ty k Γ
liftTy j<k ty γ = lift j<k (ty γ)

liftTm : ∀ {j k Γ A} → (j<k : j < k) → Tm j Γ A → Tm k Γ (liftTy j<k A)
liftTm {A = A} j<k tm γ = el→ j<k (A γ) (tm γ)

{-----------------------------------------------------------
  Contexts C is a category with a terminal element,
  where morphisms (substitutions) are functions from
  (the interpretations of) one context to another.
  Ty and Tm are Fam-valued presheaves over C,
  whose actions on substitutions are actually applying
  the substitutions to the type or term.
-----------------------------------------------------------}

_⇒_ : C → C → Set
Δ ⇒ Γ = em Δ → em Γ

id : ∀ {Γ} → Γ ⇒ Γ
id γ = γ

⟨⟩ : ∀ {Γ} → Γ ⇒ ∙
⟨⟩ {Γ} _ = tt

⟨⟩η : ∀ {Γ} → (σ : Γ ⇒ ∙) → σ ≡ ⟨⟩
⟨⟩η _ = refl

infix 30 _[_]ᵀ
_[_]ᵀ : ∀ {k Δ Γ} → Ty k Γ → Δ ⇒ Γ → Ty k Δ
(A [ σ ]ᵀ) δ = A (σ δ)

infix 30 _[_]ᵗ
_[_]ᵗ : ∀ {k Δ Γ} {A : Ty k Γ} → Tm k Γ A → (σ : Δ ⇒ Γ) → Tm k Δ (A [ σ ]ᵀ)
(a [ σ ]ᵗ) δ = a (σ δ)

infix 30 _∋_[_]ᵗ
_∋_[_]ᵗ : ∀ {k Δ Γ} → (A : Ty k Γ) → Tm k Γ A → (σ : Δ ⇒ Γ) → Tm k Δ (A [ σ ]ᵀ)
A ∋ a [ σ ]ᵗ = a [ σ ]ᵗ

{-----------------------------------------------------------
  Context comprehensions conventionally come with
  substitution extension and their projections,
  but since our contexts are inductively constructed,
  these are straightforward and rather redundant.
-----------------------------------------------------------}

⟨_,_⟩ : ∀ {k Δ Γ} {A : Ty k Γ} → (σ : Δ ⇒ Γ) → Tm k Δ (A [ σ ]ᵀ) → Δ ⇒ (Γ ▷ A)
⟨ σ , a ⟩ δ = σ δ , a δ

p : ∀ {k Γ} {A : Ty k Γ} → (Γ ▷ A) ⇒ Γ
p (γ , a) = γ

q : ∀ {k Γ} {A : Ty k Γ} → Tm k (Γ ▷ A) (A [ p ]ᵀ)
q (γ , a) = a

pqη : ∀ {k Γ} {A : Ty k Γ} → ⟨ p {k} {Γ} {A} , q {k} {Γ} {A} ⟩ ≡ λ γ → γ
pqη = refl

{-----------------------------------------------------------
  Additional structures for dependent functions,
  nondependent functions, and the empty type,
  along with the βη laws they satisfy.
  Note that Ty k Γ is equal to Tm k Γ (λ _ → Û),
  so types are also terms of U k (i.e. à la Russell).
-----------------------------------------------------------}

Pi : ∀ {j k Γ} → j < k → (A : Ty j Γ) → (B : Ty k (Γ ▷ A)) → Ty k Γ
Pi {j} {k} {Γ} j<k A B γ with wf k
... | acc< f rewrite accProp (wf j) (f j<k) = Π̂ j j<k (A γ) (λ a → B (γ , a))

dlam : ∀ {j k Γ} {j<k : j < k} {A : Ty j Γ} {B : Ty k (Γ ▷ A)}
        → Tm k (Γ ▷ A) B → Tm k Γ (Pi j<k A B)
dlam {j} {k} {Γ} {j<k} b γ with wf k
... | acc< f rewrite accProp (wf j) (f j<k) = λ a → b (γ , a)

dapp : ∀ {j k Γ} {j<k : j < k} {A : Ty j Γ} {B : Ty k (Γ ▷ A)}
        → Tm k Γ (Pi j<k A B) → (a : Tm j Γ A) → Tm k Γ (B [ ⟨ id , a ⟩ ]ᵀ)
dapp {j} {k} {Γ} {j<k} b a γ with wf k
... | acc< f rewrite accProp (wf j) (f j<k) = b γ (a γ)

Πβ : ∀ {j k Γ} {j<k : j < k} {A : Ty j Γ} {B : Ty k (Γ ▷ A)} {b : Tm k (Γ ▷ A) B} {a : Tm j Γ A}
      → dapp {j<k = j<k} (dlam b) a ≡ b [ ⟨ id , a ⟩ ]ᵗ
Πβ {j} {k} {Γ} {j<k} with wf k
... | acc< f rewrite accProp (wf j) (f j<k) = refl

{-----------------------------------------------------------
  The type of the η-equivalence law doesn't type check
  because of all the accProp nonsense in the middle,
  but we can computationally verify that:
    dlam (dapp (f [ p ]ᵗ) q) γ
    ≡ λ a → dapp (f [ p ]ᵗ) q (γ , a)         by dlam
    ≡ λ a → (f [ p ]ᵗ) (γ , a) (q (γ , a))    by dapp
    ≡ λ a → (f [ p ]ᵗ) (γ , a) a              by q
    ≡ λ a → f (p (γ , a)) a                   by _[_]ᵗ
    ≡ λ a → f γ a                             by p
    ≡ f γ                                     by Agda's η-equivalence
  It may be reassuring to note that this does hold for Arr
  definitionally as shown in →η below.
Πη : ∀ {j k Γ} {j<k : j < k} {A : Ty j Γ} {B : Ty k (Γ ▷ A)} {f : Tm k Γ (Pi j<k A B)}
      → dlam (dapp (Pi j<k A B ∋ f [ p ]ᵗ) q) ≡ f
-----------------------------------------------------------}

Arr : ∀ {k Γ} → (A B : Ty k Γ) → Ty k Γ
Arr A B γ = →̂  (A γ) (B γ)

lam : ∀ {k Γ} {A B : Ty k Γ} → Tm k (Γ ▷ A) (B [ p ]ᵀ) → Tm k Γ (Arr A B)
lam b γ a = b (γ , a)

app : ∀ {k Γ} {A B : Ty k Γ} → Tm k Γ (Arr A B) → Tm k Γ A → Tm k Γ B
app b a γ = b γ (a γ)

→β : ∀ {k Γ} {A B : Ty k Γ} {b : Tm k (Γ ▷ A) (B [ p ]ᵀ)} {a : Tm k Γ A}
      → app (lam b) a ≡ b [ ⟨ id , a ⟩ ]ᵗ
→β = refl

→η : ∀ {k Γ} {A B : Ty k Γ} {f : Tm k Γ (Arr A B)} → lam (app (Arr A B ∋ f [ p ]ᵗ) q) ≡ f
→η = refl

Empty : ∀ {k Γ} → Ty k Γ
Empty γ = ⊥̂

absurd : ∀ {k Γ} {A : Ty k Γ} → Tm k Γ Empty → Tm k Γ A
absurd b γ with () <- b γ

Type : ∀ {k Γ} → Ty k Γ
Type {k} _ = Û

TmU≡Ty : ∀ {k Γ} → Tm k Γ Type ≡ Ty k Γ
TmU≡Ty = refl

{-----------------------------------------------------------
  Modelling context membership and extracting a term.
  A more inductivey and expanded version of p/q I think.
-----------------------------------------------------------}

data _∋_ : ∀ {k} Γ → Ty k Γ → Set where
  here : ∀ {k Γ A} → Γ ▷ A ∋ A [ p {k} ]ᵀ
  there : ∀ {k Γ A B} → (_∋_ {k}) Γ A → Γ ▷ B ∋ A [ p {k} ]ᵀ

en : ∀ {k Γ A} → Γ ∋ A → Tm k Γ A
en here (γ , a) = a
en (there where?) (γ , a) = en where? γ

{-----------------------------------------------------------
  Consistency: For all levels,
  there is no inhabitant of the empty type.
-----------------------------------------------------------}

consistency : ∀ k → Tm k ∙ Empty → ⊥
consistency k b = b tt

{-----------------------------------------------------------

open import Data.Nat renaming (_<_ to _<N_)
open import Data.Fin renaming (_<_ to _<F_ ; _+_ to _+F_)

data Term (n : ℕ) : Set where
  var : Fin n → Term n
  ∗ : Term n
  Π : Term n → Level → Term (suc n) → Term n
  λᵈ : Term (suc n) → Term n
  $ᵈ : Term n → Term n → Term n
  mty : Term n
  abs : Term n → Term n

weaken : ∀ {n m} → Term n → Term (n + m)
weaken (var n) = var (inject+ _ n)
weaken ∗ = ∗
weaken (Π A j B) = Π (weaken A) j (weaken B)
weaken (λᵈ b) = λᵈ (weaken b)
weaken ($ᵈ b a) = $ᵈ (weaken b) (weaken a)
weaken mty = mty
weaken (abs b) = abs (weaken b)

infixl 30 _∷_
data Ctx : ℕ → Set where
  · : Ctx zero
  _∷_ : ∀ {n} → Ctx n → Term n → Ctx (suc n)

+1≡suc : ∀ {n} → n + 1 ≡ suc n
+1≡suc {zero} = refl
+1≡suc {suc n} = cong suc +1≡suc

get : ∀ {n} → Ctx n → Fin n → Term n
get (Γ ∷ A) zero = transp Term +1≡suc (weaken A)
get (Γ ∷ A) (suc n) = transp Term +1≡suc (weaken (get Γ n))

postulate substitute : ∀ {n : ℕ} → Term (suc n) → Term n → Term n

data _⊢_⦂_#_ {n : ℕ} (Γ : Ctx n) : Term n → Term n → Level → Set where
  TVar : ∀ k n → Γ ⊢ var n ⦂ get Γ n # k
  TType : ∀ k → Γ ⊢ ∗ ⦂ ∗ # k
  TPi : ∀ j k A B →
        j < k →
        Γ ⊢ A ⦂ ∗ # j →
        Γ ∷ A ⊢ B ⦂ ∗ # k →
        -------------------
        Γ ⊢ Π A j B ⦂ ∗ # k
  TAbs : ∀ j k A B b →
         Γ ∷ A ⊢ b ⦂ B # k →
         ----------------------
         Γ ⊢ λᵈ b ⦂ Π A j B # k
  TApp : ∀ j k A B a b →
         Γ ⊢ b ⦂ Π A j B # k →
         Γ ⊢ a ⦂ A # j →
         -------------------------------
         Γ ⊢ $ᵈ b a ⦂ substitute B a # k
  TEmpty : ∀ k → Γ ⊢ mty ⦂ ∗ # k
  TAbsurd : ∀ k B b →
            Γ ⊢ b ⦂ mty # k →
            -----------------
            Γ ⊢ abs b ⦂ B # k

-----------------------------------------------------------} 