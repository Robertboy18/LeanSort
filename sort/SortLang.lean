import sort.State


inductive AExp where
  | Const: Nat -> AExp
  | Var: VarIndex -> AExp
  | Plus: AExp -> AExp -> AExp
  deriving Repr


instance: Coe VarIndex AExp where
  coe := .Var

instance: Coe Nat AExp where
  coe := .Const


@[simp]
def State.aeval (st: State): AExp -> Nat
  | .Const n => n
  | .Plus a1 a2 => st.aeval a1 + st.aeval a2
  | .Var x => st x


declare_syntax_cat aexp
syntax num: aexp
syntax "#[" term "]": aexp
syntax aexp "+" aexp: aexp
syntax "[" term "]": aexp
syntax "[AExp|" aexp "]": term

macro_rules
  | `([AExp| $n: num ]) => `(AExp.Const $n)
  | `([AExp| #[ $t ] ]) => `(AExp.Var ((($t)): VarIndex))
  | `([AExp| [ $t ] ]) => `((($t): AExp))
  | `([AExp| $n1 + $n2]) => `(AExp.Plus [AExp| $n1 ] [AExp| $n2 ])


example: [AExp| 1 + #[1] + #[ 1 + 2 ]] = AExp.Plus (.Const 1) (.Plus (.Var 1) (.Var 3)) := by eq_refl
example: [AExp| [ (3: Nat) ] + [ (.Var 3) ] ] = (AExp.Const 3).Plus (AExp.Var 3) := by eq_refl

inductive BExp : Type where
  | True
  | False
  | Eq (a1 a2 : AExp)
  | Le (a1 a2 : AExp)
  | Not (b : BExp)
  | And (b1 b2 : BExp)
  deriving Repr


instance: Coe Bool BExp where
  coe b := match b with
  | true => .True
  | false => .False


@[simp]
def State.beval (st: State) (b: BExp): Bool := match b with
  | .True => True
  | .False => False
  | .Eq a1 a2 => (st.aeval a1).beq  (st.aeval a2)
  | .Le a1 a2 => (st.aeval a1).ble (st.aeval a2)
  | .And b1 b2 => (st.beval b1) && (st.beval b2)
  | .Not b => (st.beval b).not


declare_syntax_cat bool (behavior := symbol)
syntax "true": bool
syntax "false": bool

declare_syntax_cat bexp
syntax bool: bexp
syntax:30 aexp "==" aexp : bexp
syntax:30 aexp "<=" aexp : bexp
syntax:20 bexp:20 "&&" bexp:21 : bexp
syntax:25 "~" bexp:25 : bexp
syntax "(" bexp ")" : bexp
syntax "[" term "]" : bexp
syntax ident : bexp
syntax "[BExp|" bexp "]" : term


macro_rules
  | `([BExp| true ]) => `(BExp.True)
  | `([BExp| false ]) => `(BExp.False)
  | `([BExp| $x:aexp == $y:aexp]) => `(BExp.Eq [AExp|$x] [AExp|$y])
  | `([BExp| $x:aexp <= $y:aexp]) => `(BExp.Le [AExp|$x] [AExp|$y])
  | `([BExp| $x:bexp && $y:bexp]) => `(BExp.And [BExp|$x] [BExp|$y])
  | `([BExp| ~ $x:bexp]) => `(BExp.Not [BExp|$x])
  | `([BExp| ($x:bexp)]) => `([BExp| $x])
  | `([BExp| [$x:term] ]) => `((($x): BExp))
  | `([BExp| $x:ident ]) => `((($x): BExp))


inductive Imp: Type where
  | Skip: Imp
  | Asgn: VarIndex -> AExp -> Imp
  | Swap: VarIndex -> VarIndex -> Imp
  | Seq: Imp -> Imp -> Imp
  | If: BExp -> Imp -> Imp -> Imp
  | While: BExp -> Imp -> Imp


inductive Imp.BigStep: Imp -> State -> State -> Prop where
  | BSkip {st: State}: BigStep .Skip st st
  | BAsgn {st: State} {a n x}:
    st.aeval a = n ->
    (Imp.Asgn x a).BigStep st st![ x => n; st ]
  | BSwap {st: State} {x1 x2: VarIndex} {a1 a2 n1 n2}:
    st.aeval x1 = a1 ->
    st.aeval x1 = a2 ->
    st.aeval a1 = n1 ->
    st.aeval a2 = n2 ->
    (Imp.Swap x1 x2).BigStep st st![ a1 => n2; a2 => n1; st]
  | BSeq {c1 c2: Imp} {st1 st2 st3: State}:
    c1.BigStep st1 st2 ->
    c2.BigStep st2 st3 ->
    (c1.Seq c2).BigStep st1 st3
  | BIfTrue {b c1 c2} {st1 st2: State}:
    st1.beval b = true ->
    c1.BigStep st1 st2 ->
    (Imp.If b c1 c2).BigStep st1 st2
  | BIfFalse {b c1 c2} {st1 st2: State}:
    st1.beval b = false ->
    c2.BigStep st1 st2 ->
    (Imp.If b c1 c2).BigStep st1 st2
  | BWhileFalse {b c} {st: State}:
    st.beval b = false ->
    (Imp.While b c).BigStep st st
  | BWhileTrue {b c} {st1 st2 st3: State}:
    st1.beval b = true ->
    c.BigStep st1 st2 ->
    (Imp.While b c).BigStep st2 st3 ->
    (Imp.While b c).BigStep st1 st3


declare_syntax_cat imp
syntax "A|" aexp: imp
syntax "B|" bexp: imp
syntax "<{" imp "}>": term

syntax:100 "skip": imp
syntax:100 "#[" term "]" ":=" aexp:15 : imp
syntax:100 "swap" "#[" term "]" "#[" term "]": imp
syntax:100 "(" imp ")" : imp
syntax:10 imp ";" imp : imp
syntax:11 "if" bexp:5 "then" imp:5 "else" imp:5 "end": imp
syntax:11 "while" bexp:5 "do" imp:5 "end": imp
syntax term: imp


macro_rules
  | `(<{ skip }>) => `(Imp.Skip)
  | `(<{ #[$t] := $y:aexp }>) => `(Imp.Asgn $t [AExp|$y])
  | `(<{ swap #[$t1] #[$t2]}>) => `(Imp.Swap $t1 $t2)
  | `(<{ ( $x:imp ) }>) => `(<{ $x }>)
  | `(<{ $c1 ; $c2 }>) => `(Imp.Seq <{$c1}> <{$c2}>)
  | `(<{ if $b then $t else $f end }>) => `(Imp.If [BExp|$b] <{$t}> <{$f}>)
  | `(<{ while $b do $t end }>) => `(Imp.While [BExp|$b] <{$t}>)
  | `(<{ $t:term }>) => `($t)

namespace Playground

-- #[0] is the input
-- sum from 1 to #[0]
example := <{
  #[2] := 0;
  #[1] := 0;
  while (~ #[2] == #[0]) do
    #[1] := #[1] + #[2];
    #[2] := #[2] + 1
  end;
  swap #[0] #[1]
}>

end Playground
