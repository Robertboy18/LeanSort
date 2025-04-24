abbrev VarIndex := Nat

def State := VarIndex -> Nat

@[simp]
def State.empty (v: Nat): State := fun _ => v


@[simp]
def State.update (m: State) (x: VarIndex) (v: Nat): State
  := fun x' => if x' == x then v else m x'


declare_syntax_cat state
syntax term: state
syntax "st![" "]": term
syntax "st![" state "]": term
syntax "_" "=>" term: state
syntax term "=>" term ";" state: state
syntax term "=>" term: state

macro_rules
  | `(st![ ]) =>`(State.empty)
  | `(st![ $m:term ]) =>`($m)
  | `(st![ _ => $v:term ]) => `(State.empty $v)
  | `(st![ $x:term => $v:term ; $m:state ]) => `(st![$m].update $x $v)
  | `(st![ $x:term => $v:term ]) => `(State.update State.empty $x $v)


theorem State.apply_empty {x: Nat} {v: Nat}:
  st![_ => v] x = v := by
    simp[empty]



theorem State.update_eq {m : State} {x v}:
  st![x => v ; m] x = v := by
    simp[update]


theorem State.update_neq {m: State} {x1 x2 v}:
  x1 ≠ x2 -> st![x1 => v; m] x2 = m x2 := by
    intros H
    simp [update]
    intros K
    symm at K
    contradiction


theorem State.update_shadow {m : State} {x v1 v2}:
  st![x => v2 ; x => v1 ; m] = st![x => v2 ; m]
:= by
  apply funext
  intros y
  cases (y.decEq x) with
  | isTrue E =>
    simp [update, E]
  | isFalse NE =>
    simp [update, NE]


theorem State.update_same {m : State} {x}:
  st![x => m x ; m] = m
:= by
  apply funext
  intros y
  cases (y.decEq x) with
  | isTrue E =>
    simp [update, E]
  | isFalse NE =>
    simp [update, NE]


theorem State.update_permute {m : State} {x1 x2 v1 v2}:
  x1 ≠ x2 ->
  st![x1 => v1 ; x2 => v2 ; m] =  st![x1 => v1 ; x2 => v2 ; m]
:= by
  intros H
  apply funext
  intros y
  simp [update]
