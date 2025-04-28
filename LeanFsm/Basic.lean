import Std.Tactic.BVDecide

namespace LeanFsm

inductive S where
| s0 : S
| s1 : S
| s2 : S
| s3 : S
deriving Repr

open S -- make the variants s0, ... available

def next (s:S) (ta tb: Bool): S :=
match s, ta, tb with
| s0, false, _     => s1
| s0, true , _     => s0
| s1, _    , _     => s2
| s2, _    , false => s3
| s2, _    , true  => s2
| s3, _    , _     => s0

#reduce (next s0 false false)
#reduce (next s0 false true)

theorem s0_sure : ∀ tb, next s0 false tb = s1:=
  by
    simp [next]



def es (s:S) : BitVec 2 :=
match s with
| s0 => 0b00
| s1 => 0b01
| s2 => 0b11
| s3 => 0b10

#eval ((es s1)[1])
#eval ((es s1)[0])

def ds (s:BitVec 2) : S :=
match s with
| 0b00 => s0
| 0b01 => s1
| 0b11 => s2
| 0b10 => s3

#eval (ds 0b10)

theorem de : ∀ s, ds (es s) = s :=
  by
    intro
    rename_i s
    cases s
    . simp [es, ds]
    . simp [es, ds]
    . simp [es, ds]
    . simp [es, ds]

theorem de_alt : ∀ s, ds (es s) = s :=
  by
    intro
    rename_i s
    cases s  <;> simp [es, ds]

inductive O where
| green  : O
| yellow : O
| red    : O
deriving Repr

open O
def eo (o:O) : BitVec 2 :=
match o with
| green  => 0b00
| yellow => 0b01
| red    => 0b10

def out (s: S): O × O :=
match s with
| s0 => (green , red)
| s1 => (yellow, red)
| s2 => (red   , green)
| s3 => (red   , yellow)

#eval (out s0)
#eval (
  let (a, b) := out s0
  let a_bv := eo a
  let b_bv := eo b
  (a_bv[1], a_bv[0], b_bv[1], b_bv[0])
  )
