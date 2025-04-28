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

theorem s0_quant : ∀ tb, next s0 false tb = s1:=
  by
    simp [next]

-- Gray encoding
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

theorem safety : ∀ s,
  match out s with
  | (green, green) => false
  | (_    , _    ) => true
  := by
    intro s
    cases s <;> simp [out]

def trans (s: S) (i: List (Bool × Bool)) : S :=
  match i with
  | [] => s
  | (ta, tb) :: il => trans (next s ta tb) il


-- proof that for any state there is at least one path
-- to any other state, thus liveness holds (its never "stuck")
theorem liveness: ∀ (s s': S), ∃ (i: List (Bool × Bool)),
  trans s i = s'
  := by
    intro s s'
    cases s <;> cases s'
    . -- s0 -> s0
      exists []
    . -- s0 -> s1
      exists [(false, default)]
    . -- s0 -> s1 -> s2
      exists [(false, default), (default, default)]
    . -- s0 -> s1 -> s2 -> s3
      exists [(false, default), (default, default), (default, false)]
    . -- s1 -> s2 -> s3 -> s0
      exists [(default, default), (default, false), (default, default)]
    . -- s1 -> s1
      exists []
    . -- s1 -> s2
      exists [(default, default)]
    . -- s1 -> s2 -> s3
      exists [(default, default), (default, false)]
    . -- s2 -> s3 -> s0
      exists [(default, false), (default, default)]
    . -- s2 -> s3 -> s0 -> s1
      exists [(default, false), (default, default), (false, default)]
    . -- s2 -> s2
      exists []
    . -- s2 -> s3
      exists [(default, default)]
    . -- s3 -> s0
      exists [(default, default)]
    . -- s3 -> s0 -> s1
      exists [(default, default), (false, default)]
    . -- s3 -> s0 -> s1 -> s2
      exists [(default, default), (false, default), (default, default)]
    . -- s3 -> s3
      exists []
