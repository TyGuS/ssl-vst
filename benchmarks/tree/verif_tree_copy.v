
Require Import VST.floyd.proofauto.
Require Import common_predicates.
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









Definition tree_copy_spec :=
  DECLARE _tree_copy
   WITH r: val, x: val, s: (list Z), a: tree_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((r : val)); is_pointer_or_null((x : val)) )
   PARAMS(r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x : val))] (r : val)); (tree (x : val) (s : list Z) (a : tree_card)))
   POST[ tvoid ]
   EX y: val,
   PROP( is_pointer_or_null((y : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (r : val)); (tree (x : val) (s : list Z) (a : tree_card)); (tree (y : val) (s : list Z) (a : tree_card))).






Definition Gprog : funspecs :=
  ltac:(with_library prog [tree_copy_spec; malloc_spec]).


Lemma body_tree_copy : semax_body Vprog Gprog f_tree_copy tree_copy_spec.
Proof.

start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename x into x2.
forward.
forward_if.

 - {
assert_PROP (a = tree_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert .
assert_PROP (((x2 : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists nullval.
ssl_entailer.
rewrite (unfold_tree_card_0 ) at 1.
ssl_entailer.
rewrite (unfold_tree_card_0 ) at 1.
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_561 _alpha_560, a = tree_card_2 _alpha_561 _alpha_560) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert _alpha_561x2 _alpha_560x2.
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
assert_PROP(is_pointer_or_null((r : val))). { entailer!. }
assert_PROP(is_pointer_or_null((lx22 : val))). { entailer!. }
forward_call ((r : val), (lx22 : val), (s1x2 : list Z), (_alpha_560x2 : tree_card)).
Intros y1.
assert_PROP(is_pointer_or_null((lx22 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((y1 : val))). { entailer!. }
try rename y1 into y12.
forward.
forward.
assert_PROP(is_pointer_or_null((r : val))). { entailer!. }
assert_PROP(is_pointer_or_null((rx22 : val))). { entailer!. }
forward_call ((r : val), (rx22 : val), (s2x2 : list Z), (_alpha_561x2 : tree_card)).
Intros y2.
assert_PROP(is_pointer_or_null((rx22 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((y2 : val))). { entailer!. }
try rename y2 into y22.
forward.
forward_call (tarray (Tunion _sslval noattr) 3).
Intros y3.
assert_PROP (isptr y3). { entailer!. }
forward.
forward.
forward.
forward.
forward; entailer!.
Exists (y3 : val).
ssl_entailer.
rewrite (unfold_tree_card_2 (_alpha_561x2 : tree_card) (_alpha_560x2 : tree_card)) at 1.
Exists (vx22 : Z).
Exists (s2x2 : list Z).
Exists (rx22 : val).
Exists (s1x2 : list Z).
Exists (lx22 : val).
ssl_entailer.
rewrite (unfold_tree_card_2 (_alpha_561x2 : tree_card) (_alpha_560x2 : tree_card)) at 1.
Exists (vx22 : Z).
Exists (s2x2 : list Z).
Exists (y22 : val).
Exists (s1x2 : list Z).
Exists (y12 : val).
ssl_entailer.

}

Qed.