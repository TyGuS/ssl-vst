
Require Import VST.floyd.proofauto.
Require Import common_predicates.
Require Import tree_free.
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











Definition tree_free_spec :=
  DECLARE _tree_free
   WITH x: val, s: (list Z), _alpha_549: tree_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x : val)) )
   PARAMS(x)
   SEP ((tree (x : val) (s : list Z) (_alpha_549 : tree_card)))
   POST[ tvoid ]
   PROP(  )
   LOCAL()
   SEP ().






Definition Gprog : funspecs :=
  ltac:(with_library prog [tree_free_spec; free_spec]).


Lemma body_tree_free : semax_body Vprog Gprog f_tree_free tree_free_spec.
Proof.

start_function.
ssl_open_context.
forward_if.

 - {
assert_PROP (_alpha_549 = tree_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert .
assert_PROP (((x : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.

}
 - {
assert_PROP (exists _alpha_545 _alpha_544, _alpha_549 = tree_card_2 _alpha_545 _alpha_544) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert _alpha_545x _alpha_544x.
assert_PROP ((~ ((x : val) = nullval))). { entailer!. }
Intros vx s2x rx s1x lx.
let ssl_var := fresh in assert_PROP(s = ((([(vx : Z)] : list Z) ++ (s1x : list Z)) ++ (s2x : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx into vx2.
forward.
try rename lx into lx2.
forward.
try rename rx into rx2.
forward.
assert_PROP(is_pointer_or_null((lx2 : val))). { entailer!. }
forward_call ((lx2 : val), (s1x : list Z), (_alpha_544x : tree_card)).
assert_PROP(is_pointer_or_null((rx2 : val))). { entailer!. }
forward_call ((rx2 : val), (s2x : list Z), (_alpha_545x : tree_card)).
forward_call (tarray (Tunion _sslval noattr) 3, x).
forward; entailer!.

}

Qed.