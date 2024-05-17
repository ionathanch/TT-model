import «TT-model».typing

open Term

@[simp]
def idType k := (pi (lvl (lof k)) (pi (𝒰 (var 0)) (pi (var 0) (var 1))))

-- idid : ((j : Level< (lof 4)) → (A : 𝒰 j) → A → A) → ((j : Level< (lof 3)) → (A : 𝒰 j) → A → A)
-- idid ≔ λ id. id (lof 3) ((j : Level< (lof 3)) → (A : 𝒰 j) → A → A) (λ j. id j)
-- All of the `sorry`s are boring proofs about context well formedness
def idid : ⬝ ⊢ (abs (app (app ((app (var 0) (lof 3))) (idType 3)) (abs (app (var 1) (var 0))))) ∶ (pi (idType 4) (idType 3)) := by
  apply Wtf.abs (k := lof 4)
  . apply Wtf.pi
    . apply Wtf.pi
      . apply Wtf.lvl; apply @Wtf.lof _ 4 5; omega
      . apply Wtf.pi
        . apply Wtf.𝒰
          . sorry
          . apply Wtf.var
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
      . apply @Wtf.lof _ 3; omega
      . apply Wtf.pi
        . apply Wtf.lvl; apply @Wtf.lof _ 3 4; omega
        . apply Wtf.pi
          . apply Wtf.𝒰
            . sorry
            . apply Wtf.var
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
        . apply Wtf.lof; omega
        . simp; exact ⟨rfl, rfl⟩
      . apply Wtf.pi
        . apply Wtf.lvl
          have lt : 3 < 4 := by omega
          apply Wtf.lof lt
        . apply Wtf.pi
          . apply Wtf.𝒰
            . sorry
            . apply Wtf.var
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
        . apply Wtf.lvl; apply @Wtf.lof _ 3 4; omega
        . apply Wtf.pi
          . apply Wtf.𝒰
            . sorry
            . apply Wtf.var
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
          . apply Wtf.lof; omega
        . simp
    . simp
