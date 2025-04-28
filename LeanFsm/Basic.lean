import Std.Tactic.BVDecide

namespace LeanFsm

inductive S where
| s0 : S
| s1 : S
| s2 : S
| s3 : S

open S -- make the variants s0, ... available

def next (s:S) (ta tb: Bool): S :=
match s, ta, tb with
| s0, false, _     => s1
| s0, true , _     => s0
| s1, _    , _     => s2
| s2, _    , false => s3
| s2, _    , true  => s2
| s3, _    , _     => s0

#reduce (next .s0 false false)
#reduce (next .s0 false true)

def e (s:S) : BitVec 2 :=
match s with
| s0 => 0b00
| s1 => 0b01
| s2 => 0b10
| s3 => 0b11

#eval (e s2)

def d (s:BitVec 2) : S :=
match s with
| 0b00 => s0
| 0b01 => s1
| 0b10 => s2
| 0b11 => s3

#eval (d 10)

theorem de : ∀ s, d (e s) = s :=
  by
    intro
    rename_i s
    cases s
    . simp [e, d]
    . simp [e, d]
    . simp [e, d]
    . simp [e, d]

theorem de_alt : ∀ s, d (e s) = s :=
  by
    intro
    rename_i s
    cases s  <;> simp [e, d]
