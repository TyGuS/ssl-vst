
Require Import VST.floyd.proofauto.
Require Import common_predicates.
Require Import sll_free.
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











Definition sll_free_spec :=
  DECLARE _sll_free
   WITH x: val, s: (list Z), _alpha_530: sll_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x : val)) )
   PARAMS(x)
   SEP ((sll (x : val) (s : list Z) (_alpha_530 : sll_card)))
   POST[ tvoid ]
   PROP(  )
   LOCAL()
   SEP ().






Definition Gprog : funspecs :=
  ltac:(with_library prog [sll_free_spec; free_spec]).


Lemma body_sll_free : semax_body Vprog Gprog f_sll_free sll_free_spec.
Proof.

start_function.
ssl_open_context.
forward_if.

 - {
assert_PROP (_alpha_530 = sll_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert .
assert_PROP (((x : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.

}
 - {
assert_PROP (exists _alpha_529, _alpha_530 = sll_card_1 _alpha_529) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert _alpha_529x.
assert_PROP ((~ ((x : val) = nullval))). { entailer!. }
Intros vx s1x nxtx.
let ssl_var := fresh in assert_PROP(s = (([(vx : Z)] : list Z) ++ (s1x : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx into vx2.
forward.
try rename nxtx into nxtx2.
forward.
assert_PROP(is_pointer_or_null((nxtx2 : val))). { entailer!. }
forward_call ((nxtx2 : val), (s1x : list Z), (_alpha_529x : sll_card)).
forward_call (tarray (Tunion _sslval noattr) 2, x).
forward; entailer!.

}

Qed.