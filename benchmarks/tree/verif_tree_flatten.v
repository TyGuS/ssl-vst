
Require Import VST.floyd.proofauto.
Require Import common_predicates.
Require Import tree_flatten.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.



Definition free_spec :=
  DECLARE _free
          WITH ty: type, x: val
                              PRE  [ (tptr tvoid) ]
                              PROP()
                              PARAMS(x)
                              SEP (data_at_ Tsh ty x)
                              POST [ Tvoid ]
                              PROP()
                              LOCAL()
                              SEP (emp).



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






Definition sll_append_spec :=
  DECLARE _sll_append
   WITH x1: val, ret: val, _alpha_555: sll_card, x2: val, s2: (list Z), _alpha_556: sll_card, s1: (list Z)
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x1 : val)); is_pointer_or_null((ret : val)); is_pointer_or_null((x2 : val)) )
   PARAMS(x1; ret)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x2 : val))] (ret : val)); (sll (x1 : val) (s1 : list Z) (_alpha_555 : sll_card)); (sll (x2 : val) (s2 : list Z) (_alpha_556 : sll_card)))
   POST[ tvoid ]
   EX y: val,
   EX s: (list Z),
   EX _alpha_557: sll_card,
   PROP( ((s : list Z) = ((s1 : list Z) ++ (s2 : list Z))); is_pointer_or_null((y : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (ret : val)); (sll (y : val) (s : list Z) (_alpha_557 : sll_card))).



Definition tree_flatten_spec :=
  DECLARE _tree_flatten
   WITH z: val, x: val, s: (list Z), _alpha_558: tree_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((z : val)); is_pointer_or_null((x : val)) )
   PARAMS(z)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x : val))] (z : val)); (tree (x : val) (s : list Z) (_alpha_558 : tree_card)))
   POST[ tvoid ]
   EX y: val,
   EX _alpha_559: sll_card,
   PROP( is_pointer_or_null((y : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (z : val)); (sll (y : val) (s : list Z) (_alpha_559 : sll_card))).






Definition Gprog : funspecs :=
  ltac:(with_library prog [tree_flatten_spec; free_spec; malloc_spec;sll_append_spec]).


Lemma body_tree_flatten : semax_body Vprog Gprog f_tree_flatten tree_flatten_spec.
Proof.

start_function.
ssl_open_context.
assert_PROP (isptr z). { entailer!. }
try rename x into x2.
forward.
forward_if.

 - {
assert_PROP (_alpha_558 = tree_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert .
assert_PROP (((x2 : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists nullval.
Exists (sll_card_0  : sll_card).
ssl_entailer.
rewrite (unfold_sll_card_0 ) at 1.
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_551 _alpha_550, _alpha_558 = tree_card_2 _alpha_551 _alpha_550) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert _alpha_551x2 _alpha_550x2.
assert_PROP ((~ ((x2 : val) = nullval))). { entailer!. }
Intros vx2 s2x2 rx2 s1x2 lx2.
let ssl_var := fresh in assert_PROP(s = ((([(vx2 : Z)] : list Z) ++ (s1x2 : list Z)) ++ (s2x2 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx2 into vx22.
forward.
try rename lx2 into lx22.
forward.
try rename rx2 into rx22.
forward.
forward.
assert_PROP(is_pointer_or_null((z : val))). { entailer!. }
assert_PROP(is_pointer_or_null((lx22 : val))). { entailer!. }
forward_call ((z : val), (lx22 : val), (s1x2 : list Z), (_alpha_550x2 : tree_card)).
let ret := fresh vret in Intros ret; destruct ret as [y1 _alpha_5591].
assert_PROP(is_pointer_or_null((y1 : val))). { entailer!. }
try rename y1 into y12.
forward.
forward.
assert_PROP(is_pointer_or_null((z : val))). { entailer!. }
assert_PROP(is_pointer_or_null((rx22 : val))). { entailer!. }
forward_call ((z : val), (rx22 : val), (s2x2 : list Z), (_alpha_551x2 : tree_card)).
let ret := fresh vret in Intros ret; destruct ret as [y2 _alpha_5592].
assert_PROP(is_pointer_or_null((y2 : val))). { entailer!. }
try rename y2 into y22.
forward.
assert_PROP(is_pointer_or_null((y12 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((z : val))). { entailer!. }
assert_PROP(is_pointer_or_null((y22 : val))). { entailer!. }
forward_call ((y12 : val), (z : val), (_alpha_5591 : sll_card), (y22 : val), (s2x2 : list Z), (_alpha_5592 : sll_card), (s1x2 : list Z)).
ssl_entailer.
let ret := fresh vret in Intros ret; destruct ret as [[y3 s3] _alpha_557].
assert_PROP(is_pointer_or_null((y3 : val))). { entailer!. }
let ssl_var := fresh in assert_PROP(s3 = ((s1x2 : list Z) ++ (s2x2 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename y3 into y32.
forward.
forward_call (tarray (Tunion _sslval noattr) 2).
Intros y4.
assert_PROP (isptr y4). { entailer!. }
forward_call (tarray (Tunion _sslval noattr) 3, x2).
forward.
forward.
forward.
forward; entailer!.
Exists (y4 : val).
Exists (sll_card_1 (_alpha_557 : sll_card) : sll_card).
ssl_entailer.
rewrite (unfold_sll_card_1 (_alpha_557 : sll_card)) at 1.
Exists (vx22 : Z).
Exists ((s1x2 : list Z) ++ (s2x2 : list Z)).
Exists (y32 : val).
ssl_entailer.

}

Qed.