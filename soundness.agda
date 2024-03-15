open import common
import accessibility
import syntactics
import reduction
import typing
import semantics

module soundness
  (Level : Set)
  (_<_ : Level → Level → Set)
  (trans< : ∀ {i j k} → i < j → j < k → i < k) where
open accessibility Level _<_
open syntactics Level
open reduction Level
open typing Level _<_ trans<
open semantics Level _<_ trans<

soundVar : ∀ {σ Γ x A k} (v : V Γ) → em σ v → x ⦂ A # k ∈ Γ →
           ∃[ acc ] Σ[ u ∈ U k acc (subst σ A) ] el k acc (subst σ (var x)) u
soundVar {σ} (∷̂  acc v u) (emV , elU) (here {A = A}) =
  let p : subst σ (rename suc A) ≡ subst (σ ∘ suc) A
      p = substRename suc σ A
  in acc , transp (U _ acc) (sym p) (u (σ ∘ suc) emV) ,
     ≡-el acc (u (σ ∘ suc) emV) (sym p) elU
soundVar {σ} (∷̂  _ v _) (emV , _) (there {x = x} {A = A} where?) =
  let acc , u , elU = soundVar v emV where?
      p : subst σ (rename suc A) ≡ subst (σ ∘ suc) A
      p = substRename suc σ A
  in acc , transp (U _ acc) (sym p) u ,
     ≡-el acc u (sym p) elU

soundness : ∀ {σ Γ a A k} (acc : Acc k) (v : V Γ) → em σ v → Γ ⊢ a ⦂ A # k →
            Σ[ u ∈ U k acc (subst σ A) ] el k acc (subst σ a) u
soundness acc v emV (⊢var ⊢Γ eq where?) =
  let acc' , u , elU = soundVar v emV where?
      u' = accU acc' acc u
  in u' , accEl acc' acc u u' elU
soundness (acc< f) v emV (⊢var ⊢Γ (lt j<k) where?) =
  let acc , u , elU = soundVar v emV where?
  in cumU acc (acc< f) j<k u , cumEl acc (acc< f) j<k u elU
soundness acc v emV (⊢∗ ⊢Γ) = Û , Û
soundness {σ} acc@(acc< f) v emV (⊢Π {B = B} {k = k} j<k tA tB) =
  let u , elU = soundness (f j<k) v emV tA
  in Û , Π̂ _ j<k _ (el-U (f j<k) u elU) _
     (λ x elA →
      let u , elU = soundness {σ = x +: σ} acc
            (∷̂  (f j<k) v (λ σ emV → let u , elU = soundness (f j<k) v emV tA in el-U (f j<k) u elU))
            (emV , elA) tB
      in transp (U k acc) (substUnion σ x B) (el-U acc u elU))
soundness {σ} acc@(acc< f) v emV (⊢λᵈ {B = B} {b = b} j<k tA tb) =
  let u , elU = soundness (f j<k) v emV tA
  in Π̂ _ j<k _ (el-U (f j<k) u elU) _
     (λ x elA →
      let uB , elB = soundness {σ = x +: σ} acc
            (∷̂  (f j<k) v (λ σ emV → let u , elU = soundness (f j<k) v emV tA in el-U (f j<k) u elU))
            (emV , elA) tb
      in transp (U _ acc) (substUnion σ x B) uB) ,
     (λ x elA →
      let uB , elB = soundness {σ = x +: σ} acc
            (∷̂  (f j<k) v (λ σ emV → let u , elU = soundness (f j<k) v emV tA in el-U (f j<k) u elU))
            (emV , elA) tb
          uB' = transp (U _ acc) (substUnion σ x B) uB
          elB' = ≡-el acc uB (substUnion σ x B) elB
      in ⇒⋆-el acc uB' (⇒⋆-β σ b x) elB')
soundness {σ} acc@(acc< f) v emV (⊢$ᵈ {B = B} {b = b} {a = a} j<k tb ta) =
  let ub , elb = soundness acc v emV tb
      ua , ela = soundness (f j<k) v emV ta
      j<k' , uA , uB = invΠ-U acc ub
      ela' = accEl (f j<k) (f j<k') ua uA ela
      uB' = uB (subst σ a) ela'
      elb' = invΠ-el acc ub (subst σ b) elb (subst σ a) ela'
  in transp (U _ acc) (substDist σ a B) uB' ,
     ≡-el acc uB' (substDist σ a B) elb'
soundness acc v emV (⊢mty ⊢Γ) = Û , ⊥̂
soundness {σ} acc v emV (⊢abs {b = b} tA tb)
  with () ← (let b , elb = soundness acc v emV tb in empty acc b elb)
soundness {σ} acc v emV (⊢≈ A≈B ta _) =
  let uA , elA = soundness acc v emV ta
      Aσ⇔Bσ = ⇔-subst σ (≈-⇔ A≈B)
      uB = ⇔-U acc Aσ⇔Bσ uA
  in uB , ⇔-el acc uA uB Aσ⇔Bσ elA