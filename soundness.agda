{-# OPTIONS --rewriting #-}

open import common
import accessibility
import syntactics
import reduction
import typing
import semantics

module soundness
  (Level : Set)
  (_<_ : Level → Level → Set)
  (trans< : ∀ {i j k} → i < j → j < k → i < k)
  (open accessibility Level _<_)
  (zero : ∃[ k ] Acc k)
  (sup : ∀ i j → ∃[ k ] i < k × j < k × Acc k)
  (succ : ∀ j → ∃[ k ] j < k × Acc k) where
open syntactics Level
open reduction Level
open typing Level _<_ trans<
open semantics Level _<_ trans< sup

soundVar : ∀ {σ Γ x A} (v : V Γ) → em σ v → x ⦂ A ∈ Γ →
           ∃[ k ] Σ[ acc ∈ Acc k ] Σ[ u ∈ U k acc (subst σ A) ] el k acc (subst σ (var x)) u
soundVar {σ} (∷̂  _ w) (emV , elU) (here {A = A}) =
  let p : subst σ (rename suc A) ≡ subst (σ ∘ suc) A
      p = substRename suc σ A
      k , acc , u = w (σ ∘ suc) emV
  in k , acc , transp (U k acc) (sym p) u ,
     ≡-el acc u (sym p) elU
soundVar {σ} (∷̂  v _) (emV , _) (there {A = A} where?) =
  let k , acc , u , elU = soundVar v emV where?
      p : subst σ (rename suc A) ≡ subst (σ ∘ suc) A
      p = substRename suc σ A
  in k , acc , transp (U k acc) (sym p) u ,
     ≡-el acc u (sym p) elU

soundness : ∀ {σ Γ a A} (v : V Γ) → em σ v → Γ ⊢ a ⦂ A →
            ∃[ k ] Σ[ acc ∈ Acc k ] Σ[ u ∈ U k acc (subst σ A) ] el k acc (subst σ a) u
soundness v emV (⊢var ⊢Γ where?) = soundVar v emV where?
soundness v emV (⊢𝒰 {j} {k} ⊢Γ j<k) =
  let ℓ , k<ℓ , accℓ@(acc< _) = succ k
  in ℓ , accℓ , Û k k<ℓ , Û j j<k
soundness {σ} v emV (⊢Π {B = B} {k = k} tA tB) =
  let ℓ , accℓ , u , elU = soundness v emV tA
      acck , k<ℓ , uA = el-U accℓ u elU
      vA = λ σ emV →
             let ℓ , accℓ , u , elU = soundness v emV tA
                 acck , k<ℓ , uA = el-U accℓ u elU
             in k , acck , uA
      uB = λ x elA →
             let _ , accℓ , u , elU = soundness {σ = x +: σ} (∷̂  v vA) (emV , elA) tB
                 acck' , _ , uB = el-U accℓ u elU
                 uB' = transp (U k acck) (substUnion σ x B) uB
             in accU acck' acck uB'
  in ℓ , accℓ , Û k k<ℓ , accU< acck accℓ k<ℓ (Π̂ _ uA _ uB)
soundness {σ} v emV (⊢λᵈ {B = B} {b = b} {k = k} tAB tb) =
  let ℓ , accℓ , u , elU = soundness v emV tAB
      acck , k<ℓ , uAB = el-U accℓ u elU
      uA , uB = invΠ-U acck uAB
      vA = λ σ emV →
             let ℓ , accℓ , u , elU = soundness v emV tAB
                 acck , k<ℓ , uAB = el-U accℓ u elU
                 uA , uB = invΠ-U acck uAB
             in k , acck , uA
  in k , acck , Π̂ _ uA _ uB ,
     (λ x elA →
        let k' , acck' , uB' , elB = soundness {σ = x +: σ} (∷̂  v vA) (emV , elA) tb
            uB'' = transp (U k' acck') (substUnion σ x B) uB'
            elB' = ≡-el acck' uB' (substUnion σ x B) elB
            elB'' = ⇒⋆-el acck' uB'' (⇒⋆-β σ b x) elB'
        in el→ acck' acck uB'' (uB x elA) elB'')
soundness {σ} v emV (⊢$ᵈ {B = B} {b = b} {a = a} tb ta) =
  let kb , acckb , ub , elb = soundness v emV tb
      ka , accka , ua , ela = soundness v emV ta
      uA , uB = invΠ-U acckb ub
      ela' = el→ accka acckb ua uA ela
      uB' = uB (subst σ a) ela'
      elb' = invΠ-el acckb ub (subst σ b) elb (subst σ a) ela'
  in kb , acckb ,
     transp (U _ acckb) (substDist σ a B) uB' ,
     ≡-el acckb uB' (substDist σ a B) elb'
soundness v emV (⊢mty {k} ⊢Γ) =
  let ℓ , k<ℓ , accℓ@(acc< _) = succ k
  in ℓ , accℓ , Û k k<ℓ , ⊥̂
soundness v emV (⊢abs {b = b} tA tb)
  with () ← (let k , acck , b , elb = soundness v emV tb in empty acck b elb)
soundness v emV (⊢eq {A} {a} {b} {k} tA ta tb) =
  let ℓ , accℓ@(acc< _) , u , elU = soundness v emV tA
      acck , k<ℓ , uA = el-U accℓ u elU
      ka , accka , ua , ela = soundness v emV ta
      kb , acckb , ub , elb = soundness v emV tb
  in ℓ , accℓ , Û k k<ℓ ,
     êq _ uA _ (el→ accka acck ua uA ela) _ (el→ acckb acck ub uA elb)
soundness v emV (⊢refl ta) =
  let k , acck , ua , ela = soundness v emV ta
  in k , acck , êq _ ua _ ela _ ela , ⇒⋆-refl refl , ⇔-refl
soundness {σ} v emV (⊢J {a = a} {b = b} {p = p} {d = d} {B = B} tp tB td) =
  let kp , acckp , up , elp = soundness v emV tp
      kd , acckd , ud , eld = soundness v emV td
      p⇒⋆refl , a⇔b = inveq-el acckp up (subst σ p) elp
      Brefla⇔Bpb : subst σ (subst (refl +: a +: var) B) ⇔ subst σ (subst (p +: b +: var) B)
      Brefla⇔Bpb = transp₂ (_⇔_) (substDist₂ σ refl a B) (substDist₂ σ p b B)
                           (⇔-cong₂ (subst (↑ ↑ σ) B) (⇔-sym (⇒⋆-⇔ p⇒⋆refl)) a⇔b)
      ud' = ⇔-U acckd Brefla⇔Bpb ud
      eld' = ⇔-el acckd ud ud' Brefla⇔Bpb eld
      Jdp⇒⋆d : subst σ (J d p) ⇒⋆ subst σ d
      Jdp⇒⋆d = ⇒⋆-trans' (⇒⋆-J (⇒⋆-refl (subst σ d)) p⇒⋆refl) (⇒⋆-ι (subst σ d))
  in kd , acckd , ud' , ⇒⋆-el acckd ud' Jdp⇒⋆d eld'
soundness {σ} v emV (⊢𝔹 {k} ⊢Γ) =
  let ℓ , k<ℓ , accℓ@(acc< _) = succ k
  in ℓ , accℓ , Û k k<ℓ , 𝔹̂
soundness {σ} v emV (⊢true ⊢Γ) =
  let k , acck = zero
  in k , acck , 𝔹̂ , inj₁ (⇒⋆-refl true)
soundness {σ} v emV (⊢false ⊢Γ) =
  let k , acck = zero
  in k , acck , 𝔹̂ , inj₂ (⇒⋆-refl false)
soundness {σ} v emV (⊢if {A} {b} {a} {c} tA tb ta tc) =
  let kb , acckb , ub , elb = soundness v emV tb
      ka , accka , ua , ela = soundness v emV ta
      kc , acckc , uc , elc = soundness v emV tc
      b⇒⋆tf = inv𝔹-el acckb ub elb
  in [ (λ b⇒⋆true →
        let Atrue⇔Ab : subst σ (subst (true +: var) A) ⇔ subst σ (subst (b +: var) A)
            Atrue⇔Ab = transp₂ (_⇔_) (substDist σ true A) (substDist σ b A)
                               (⇔-cong (⇔-sym (⇒⋆-⇔ b⇒⋆true)) (⇔-refl {subst (↑ σ) A}))
            ua' = ⇔-U accka Atrue⇔Ab ua
            ela' = ⇔-el accka ua ua' Atrue⇔Ab ela
            ift⇒⋆a : subst σ (if b a c) ⇒⋆ subst σ a
            ift⇒⋆a = (⇒⋆-trans' (⇒⋆-if b⇒⋆true (⇒⋆-refl (subst σ a)) (⇒⋆-refl (subst σ c)))
                                (⇒-⇒⋆ (⇒-ift (⇒-refl (subst σ a)))))
        in ka , accka , ua' , ⇒⋆-el accka ua' ift⇒⋆a ela') ,
       (λ b⇒⋆false →
        let Afalse⇔Ab : subst σ (subst (false +: var) A) ⇔ subst σ (subst (b +: var) A)
            Afalse⇔Ab = transp₂ (_⇔_) (substDist σ false A) (substDist σ b A)
                               (⇔-cong (⇔-sym (⇒⋆-⇔ b⇒⋆false)) (⇔-refl {subst (↑ σ) A}))
            uc' = ⇔-U acckc Afalse⇔Ab uc
            elc' = ⇔-el acckc uc uc' Afalse⇔Ab elc
            iff⇒⋆c : subst σ (if b a c) ⇒⋆ subst σ c
            iff⇒⋆c = (⇒⋆-trans' (⇒⋆-if b⇒⋆false (⇒⋆-refl (subst σ a)) (⇒⋆-refl (subst σ c)))
                                (⇒-⇒⋆ (⇒-iff (⇒-refl (subst σ c)))))
        in kc , acckc , uc' , ⇒⋆-el acckc uc' iff⇒⋆c elc') ]′
     b⇒⋆tf
soundness {σ} v emV (⊢≈ A≈B ta _) =
  let k , acck , uA , elA = soundness v emV ta
      Aσ⇔Bσ = ⇔-subst σ (≈-⇔ A≈B)
      uB = ⇔-U acck Aσ⇔Bσ uA
  in k , acck , uB , ⇔-el acck uA uB Aσ⇔Bσ elA