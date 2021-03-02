
Require Import VST.floyd.proofauto.
Require Import common_predicates.
Require Import sll_copy.
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









Definition sll_copy_spec :=
  DECLARE _sll_copy
   WITH r: val, x: val, s: (list Z), a: sll_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((r : val)); is_pointer_or_null((x : val)) )
   PARAMS(r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x : val))] (r : val)); (sll (x : val) (s : list Z) (a : sll_card)))
   POST[ tvoid ]
   EX y: val,
   EX b: sll_card,
   PROP( is_pointer_or_null((y : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (r : val)); (sll (x : val) (s : list Z) (a : sll_card)); (sll (y : val) (s : list Z) (b : sll_card))).






Definition Gprog : funspecs :=
  ltac:(with_library prog [sll_copy_spec; malloc_spec]).


Lemma body_sll_copy : semax_body Vprog Gprog f_sll_copy sll_copy_spec.
Proof.

start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename x into x2.
forward.
forward_if.

 - {
assert_PROP (a = sll_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert .
assert_PROP (((x2 : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists nullval.
Exists (sll_card_0  : sll_card).
ssl_entailer.
rewrite (unfold_sll_card_0 ) at 1.
ssl_entailer.
rewrite (unfold_sll_card_0 ) at 1.
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_528, a = sll_card_1 _alpha_528) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert _alpha_528x2.
assert_PROP ((~ ((x2 : val) = nullval))). { entailer!. }
Intros vx2 s1x2 nxtx2.
let ssl_var := fresh in assert_PROP(s = (([(vx2 : Z)] : list Z) ++ (s1x2 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx2 into vx22.
forward.
try rename nxtx2 into nxtx22.
forward.
forward.
assert_PROP(is_pointer_or_null((r : val))). { entailer!. }
assert_PROP(is_pointer_or_null((nxtx22 : val))). { entailer!. }
forward_call ((r : val), (nxtx22 : val), (s1x2 : list Z), (_alpha_528x2 : sll_card)).
let ret := fresh vret in Intros ret; destruct ret as [y1 b1].
assert_PROP(is_pointer_or_null((nxtx22 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((y1 : val))). { entailer!. }
try rename y1 into y12.
forward.
forward_call (tarray (Tunion _sslval noattr) 2).
Intros y2.
assert_PROP (isptr y2). { entailer!. }
forward.
forward.
forward.
forward; entailer!.
Exists (y2 : val).
Exists (sll_card_1 (b1 : sll_card) : sll_card).
ssl_entailer.
rewrite (unfold_sll_card_1 (_alpha_528x2 : sll_card)) at 1.
Exists (vx22 : Z).
Exists (s1x2 : list Z).
Exists (nxtx22 : val).
ssl_entailer.
rewrite (unfold_sll_card_1 (b1 : sll_card)) at 1.
Exists (vx22 : Z).
Exists (s1x2 : list Z).
Exists (y12 : val).
ssl_entailer.

}

Qed.