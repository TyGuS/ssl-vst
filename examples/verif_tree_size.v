
Require Import VST.floyd.proofauto.
Require Import tree_size.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Inductive tree_card : Set :=
    | tree_card_0 : tree_card
    | tree_card_2 : tree_card -> tree_card -> tree_card.

Fixpoint tree (x: val) (s: (list val)) (self_card: tree_card) : mpred := match self_card with
    | tree_card_0  =>  !!(x = nullval) && !!(s = []) && emp
    | tree_card_2 _alpha_514 _alpha_513 => 
      EX s2 : (list val),
      EX r : val,
      EX v : Z,
      EX s1 : (list val),
      EX l : val,
 !!(~ (x = nullval)) && !!(s = (([(Vint (Int.repr v))] ++ s1) ++ s2)) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [inl (Vint (Int.repr v)); inr l; inr r] x) * (tree r s2 _alpha_514) * (tree l s1 _alpha_513)
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
 !!(~ (x = nullval)) && !!(0 <= n1) && !!(0 <= n2) && !!(n = ((1 + n1) + n2)) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [inr v; inr l; inr r] x) * (treeN r n2 _alpha_516) * (treeN l n1 _alpha_515)
end.

Definition tree_size_spec :=
  DECLARE _tree_size
   WITH x: val, r: val, n: Z, a: treeN_card
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( (0 <= n); is_pointer_or_null(x); is_pointer_or_null(r); ssl_is_valid_int(n) )
   PARAMS(x; r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inl (Vint (Int.repr 0))] r); (treeN x n a))
   POST[ tvoid ]
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inl (Vint (Int.repr n))] r); (treeN x n a)).

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
  ltac:(with_library prog [tree_size_spec]).

Lemma body_tree_size : semax_body Vprog Gprog f_tree_size tree_size_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
forward_if.
 - {
assert_PROP (a = treeN_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card treeN ssl_card_assert .
assert_PROP ((x = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(n = nullval) as ssl_var; try rewrite ssl_var. { entailer!. }
forward; entailer!.
simpl (treeN _ _ ((treeN_card_0  : treeN_card))) at 1.
entailer!.

}
 - {
assert_PROP (exists _alpha_516 _alpha_515, a = treeN_card_2 _alpha_516 _alpha_515) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card treeN ssl_card_assert _alpha_516x _alpha_515x.
assert_PROP ((~ (x = nullval))). { entailer!. }
Intros vx rx n1x lx n2x.
let ssl_var := fresh in assert_PROP(n = ((1 + n1x) + n2x)) as ssl_var; try rewrite ssl_var. { entailer!. }
try rename vx into vx2.
assert_PROP (is_pointer_or_null vx2). { entailer!. }
try rename lx into lx2.
forward.
assert_PROP (is_pointer_or_null lx2). { entailer!. }
try rename rx into rx2.
forward.
assert_PROP (is_pointer_or_null rx2). { entailer!. }
try rename a1 into _alpha_515x.
try rename x1 into lx2.
try rename n1 into n1x.
try rename r1 into r.
forward_call (lx2, r, n1x, _alpha_515x).
try rename n1x into n1x2.
forward.
try rename a2 into _alpha_516x.
try rename n2 into n2x.
try rename x2 into rx2.
try rename r2 into r.
forward.
forward_call (rx2, r, n2x, _alpha_516x).
try rename n2x into n2x2.
forward.
try rename _alpha_515x1 into _alpha_515x.
try rename lx1 into lx2.
try rename n11x into n1x2.
try rename _alpha_516x1 into _alpha_516x.
try rename n21x into n2x2.
try rename r3x into rx2.
forward.
try rename vx1 into vx2.
forward; entailer!.
simpl (treeN _ _ ((treeN_card_2 _alpha_516 _alpha_515 : treeN_card))) at 1.
Exists vx2.
Exists r3.
Exists n11.
Exists lx2.
Exists n21.
entailer!.

}
Qed.