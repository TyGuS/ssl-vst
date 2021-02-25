
Require Import VST.floyd.proofauto.
Require Import tree_copy.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition malloc_spec :=
  DECLARE _malloc
        WITH t: type
        PRE [ tuint ]
        PROP()
        PARAMS(Vint (Int.repr (sizeof t)))
        SEP()
        POST [tptr tvoid] EX p:_,
        PROP()
        RETURN(p)
        SEP(data_at_ Tsh t p).

Inductive tree_card : Set :=
    | tree_card_0 : tree_card
    | tree_card_2 : tree_card -> tree_card -> tree_card.

Fixpoint tree (x: val) (s: (list val)) (self_card: tree_card) : mpred := match self_card with
    | tree_card_0  =>  !!(x = nullval) && !!(s = ([])) && emp
    | tree_card_2 _alpha_514 _alpha_513 => 
      EX s2 : (list val),
      EX r : val,
      EX v : Z,
      EX s1 : (list val),
      EX l : val,
 !!(~ (x = nullval)) && !!(s = ((([(Vint (Int.repr v))]) ++ s1) ++ s2)) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) ([inl (Vint (Int.repr v)); inr l; inr r]) x) * (tree r s2 (_alpha_514 : tree_card)) * (tree l s1 (_alpha_513 : tree_card))
end.

Inductive treeN_card : Set :=
    | treeN_card_0 : treeN_card
    | treeN_card_2 : treeN_card -> treeN_card -> treeN_card.

Fixpoint treeN (x: val) (n: Z) (self_card: treeN_card) : mpred := match self_card with
    | treeN_card_0  =>  !!(x = nullval) && !!(n = 0) && emp
    | treeN_card_2 _alpha_516 _alpha_515 => 
      EX v : val,
      EX r : val,
      EX n1 : Z,
      EX l : val,
      EX n2 : Z,
 !!(~ (x = nullval)) && !!(0 <= n1) && !!(0 <= n2) && !!(n = ((1 + n1) + n2)) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) ([inr v; inr l; inr r]) x) * (treeN r n2 (_alpha_516 : treeN_card)) * (treeN l n1 (_alpha_515 : treeN_card))
end.

Definition tree_copy_spec :=
  DECLARE _tree_copy
   WITH r: val, x: val, s: (list val), a: tree_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null(r); is_pointer_or_null(x) )
   PARAMS(r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr x] r); (tree x s (a : tree_card)))
   POST[ tvoid ]
   EX y: val,
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr y] r); (tree y s (a : tree_card)); (tree x s (a : tree_card))).

Lemma tree_x_valid_pointerP x s self_card: tree x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve tree_x_valid_pointerP : valid_pointer.
Lemma tree_local_factsP x s self_card :
  tree x s self_card|-- !!((((x = nullval)) -> (self_card = tree_card_0))/\(((~ (x = nullval))) -> (exists _alpha_514 _alpha_513, self_card = tree_card_2 _alpha_514 _alpha_513))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve tree_local_factsP : saturate_local.
Lemma treeN_x_valid_pointerP x n self_card: treeN x n self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve treeN_x_valid_pointerP : valid_pointer.
Lemma treeN_local_factsP x n self_card :
  treeN x n self_card|-- !!((((x = nullval)) -> (self_card = treeN_card_0))/\(((~ (x = nullval))) -> (exists _alpha_516 _alpha_515, self_card = treeN_card_2 _alpha_516 _alpha_515))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve treeN_local_factsP : saturate_local.
Definition Gprog : funspecs :=
  ltac:(with_library prog [tree_copy_spec; malloc_spec]).

Lemma body_tree_copy : semax_body Vprog Gprog f_tree_copy tree_copy_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename x into x2.
forward.
assert_PROP (is_pointer_or_null x2). { entailer!. }
forward_if.
 - {
assert_PROP (a = tree_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert .
assert_PROP ((x2 = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([])) as ssl_var; try rewrite ssl_var. { entailer!. }
forward; entailer!.
try evar (a : tree_card).
try evar (a : tree_card).
Exists nullval.
entailer!.
try instantiate (a := (tree_card_0  : tree_card)).
try simpl (tree _ _ ((a : tree_card))) at 1.
try instantiate (a := (tree_card_0  : tree_card)).
try simpl (tree _ _ ((a : tree_card))) at 1.
simpl.
entailer!.
}
 - {
assert_PROP (exists _alpha_514 _alpha_513, a = tree_card_2 _alpha_514 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert _alpha_514x2 _alpha_513x2.
assert_PROP ((~ (x2 = nullval))). { entailer!. }
Intros s2x2 rx2 vx2 s1x2 lx2.
let ssl_var := fresh in assert_PROP(s = ((([(Vint (Int.repr vx2))]) ++ s1x2) ++ s2x2)) as ssl_var; try rewrite ssl_var. { entailer!. }
try rename vx2 into vx22.
forward.
try rename lx2 into lx22.
forward.
assert_PROP (is_pointer_or_null lx22). { entailer!. }
try rename rx2 into rx22.
forward.
assert_PROP (is_pointer_or_null rx22). { entailer!. }
try rename a1 into _alpha_513x2.
try rename x1 into lx22.
try rename s1 into s1x2.
try rename r1 into r.
forward.
forward_call (r, lx22, s1x2, _alpha_513x2).
Intros y1.
try rename y1 into y12.
forward.
try rename a2 into _alpha_514x2.
try rename x3 into rx22.
try rename s2 into s2x2.
try rename r2 into r.
forward.
forward_call (r, rx22, s2x2, _alpha_514x2).
Intros y2.
try rename y2 into y22.
forward.
try rename _alpha_513x21 into _alpha_513x2.
try rename lx21 into lx22.
try rename s11x2 into s1x2.
try rename _alpha_514x21 into _alpha_514x2.
try rename r3x2 into rx22.
try rename s21x2 into s2x2.
try rename _alpha_513y into _alpha_513x2.
try rename ly into y12.
try rename s11y into s1x2.
try rename _alpha_514y into _alpha_514x2.
try rename r3y into y22.
try rename s21y into s2x2.
forward_call (tarray (Tunion _sslval noattr) 3).
Intros y3.
assert_PROP (isptr y3). { entailer!. }
forward.
forward.
forward.
try rename vx21 into vx22.
forward.
forward; entailer!.
Exists y3.
entailer!.
try instantiate (a := (tree_card_2 (_alpha_514 : tree_card) (_alpha_513 : tree_card) : tree_card)).
simpl (tree _ _ ((a : tree_card))) at 1 || simpl (tree _ _ (tree_card_2 (_alpha_514x2 : tree_card) (_alpha_513x2 : tree_card) : tree_card)) at 1.
Exists s2x2.
Exists y22.
Exists vx22.
Exists s1x2.
Exists y12.
try instantiate (a := (tree_card_2 (_alpha_514 : tree_card) (_alpha_513 : tree_card) : tree_card)).
simpl (tree _ _ ((a : tree_card))) at 1 || simpl (tree _ _ (tree_card_2 (_alpha_514x2 : tree_card) (_alpha_513x2 : tree_card) : tree_card)) at 1.
Exists s2x2.
Exists rx22.
Exists vx22.
Exists s1x2.
Exists lx22.
entailer!.
}
Qed.
