import «TT-model».typing

open Term

set_option autoImplicit false
set_option pp.fieldNotation false

@[simp]
def idType k := (pi (lvl (lof k)) (pi (𝒰 (var 0)) (pi (var 0) (var 1))))

-- idpoly : (j : Level< 69) → (A : 𝒰 j) → A → A
-- idpoly ≔ λ j A x. x
theorem idpoly : ⬝ ⊢ (abs (abs (abs (var 0)))) ∶ idType 69 := by
  apply Wtf.abs (k := lof 69)
  . apply Wtf.pi
    . apply Wtf.lvl; apply Wtf.lof (k := 70); sorry; simp
    . apply Wtf.pi
      . apply Wtf.𝒰
        apply Wtf.var
        . sorry
        . apply inHere; rfl
      . apply Wtf.pi
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inHere; rfl
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
  . apply Wtf.abs
    . apply Wtf.pi
      . apply Wtf.𝒰
        apply Wtf.var
        . sorry
        . apply inHere; rfl
      . apply Wtf.pi
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inHere; rfl
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
    . apply Wtf.abs
      . apply Wtf.pi
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inHere; rfl
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
      . apply Wtf.var
        . sorry
        . apply inHere; rfl

-- idid : ((j : Level< (lof 4)) → (A : 𝒰 j) → A → A) → ((j : Level< (lof 3)) → (A : 𝒰 j) → A → A)
-- idid ≔ λ id. id (lof 3) ((j : Level< (lof 3)) → (A : 𝒰 j) → A → A) (λ j. id j)
-- All of the `sorry`s are boring proofs about context well formedness
theorem idid : ⬝ ⊢ (abs (app (app ((app (var 0) (lof 3))) (idType 3)) (abs (app (var 1) (var 0))))) ∶ (pi (idType 4) (idType 3)) := by
  apply Wtf.abs (k := lof 4)
  . apply Wtf.pi
    . apply Wtf.pi
      . apply Wtf.lvl; apply @Wtf.lof _ _ _ 5; sorry; simp
      . apply Wtf.pi
        . apply Wtf.𝒰
          apply Wtf.var
          . sorry
          . apply inHere; rfl
        . apply Wtf.pi
          . apply Wtf.sub
            . apply Wtf.var
              . sorry
              . apply inThere; apply inHere; rfl; rfl
            . apply Wtf.var
              . sorry
              . apply inHere; rfl
          . apply Wtf.sub
            . apply Wtf.var
              . sorry
              . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
            . apply Wtf.var
              . sorry
              . apply inThere; apply inHere; rfl; rfl
    . apply Wtf.sub
      . apply @Wtf.lof _ _ 3; sorry; simp
      . apply Wtf.pi
        . apply Wtf.lvl; apply @Wtf.lof _ _ _ 4; sorry; simp
        . apply Wtf.pi
          . apply Wtf.𝒰
            apply Wtf.var
            . sorry
            . apply inHere; rfl
          . apply Wtf.pi
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inHere; rfl
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
  . apply wtfApp
    . apply wtfApp
      . apply wtfApp
        . apply Wtf.var
          . sorry
          . apply inHere; rfl
        . apply Wtf.lof; sorry; simp
        . simp; exact ⟨rfl, rfl⟩
      . apply Wtf.pi
        . apply Wtf.lvl
          apply @Wtf.lof _ _ _ 4; sorry; simp
        . apply Wtf.pi
          . apply Wtf.𝒰
            apply Wtf.var
            . sorry
            . apply inHere; rfl
          . apply Wtf.pi
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inHere; rfl
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
      . simp; exact ⟨rfl, rfl⟩
    . apply Wtf.abs (k := lof 3)
      . apply Wtf.pi
        . apply Wtf.lvl; apply @Wtf.lof _ _ _ 4; sorry; simp
        . apply Wtf.pi
          . apply Wtf.𝒰
            apply Wtf.var
            . sorry
            . apply inHere; rfl
          . apply Wtf.pi
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inHere; rfl
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
      . apply wtfApp
        . apply Wtf.var
          . sorry
          . apply inThere; apply inHere; rfl; rfl
        . apply Wtf.trans
          . apply Wtf.var
            . sorry
            . apply inHere; rfl
          . apply Wtf.lof; sorry; simp
        . simp
    . simp
