Require Import VST.floyd.proofauto.
Require Import listcopy.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* Notation "a |~> b" := *)
(*   (data_at Tsh (tarray (Tunion _sslval noattr) 1) [b] a) (at level 1). *)
(* Notation "a '|~>' '[' b ';' c ']'" := *)
(*   (data_at Tsh (tarray (Tunion _sslval noattr) 2) [b; c] a) (at level 1). *)
(* Notation "'$(int)(' a ')'" := (inl (Vint (Int.repr a))). *)
(* Notation "'$(ptr)(' a ')'" := (inr a). *)
(* Notation "'int[' n ']'" := (tarray (Tunion _sslval noattr) n). *)


Inductive lseg_card : Set :=
    | lseg_card_0 : lseg_card
    | lseg_card_1 : lseg_card -> lseg_card.




Fixpoint lseg (x: val) (s: (list val)) (self_card: lseg_card) : mpred := match self_card with
    | lseg_card_0  =>  !!(x = nullval) && !!(s = []) && emp
    | lseg_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list val),
      EX nxt : val,
 !!(~ (x = nullval)) && !!(s = ([(Vint (Int.repr v))] ++ s1)) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [inl (Vint (Int.repr v)); inr nxt] x) * (lseg nxt s1 _alpha_513)
end.

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

Definition listcopy_spec :=
  DECLARE _listcopy
   WITH r: val, x: val, s: (list val), _alpha_514: lseg_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null(r); is_pointer_or_null(x) )
   PARAMS(r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr x] r); (lseg x s _alpha_514))
   POST[ tvoid ]
   EX _alpha_516: lseg_card,
   EX y: val,
   EX _alpha_515: lseg_card,
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr y] r); (lseg y s _alpha_516); (lseg x s _alpha_515)).

Lemma lseg_x_valid_pointerP x s self_card: lseg x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve lseg_x_valid_pointerP : valid_pointer.
Lemma lseg_local_factsP x s self_card :
  lseg x s self_card  |-- !!((((x = nullval)) -> (self_card = lseg_card_0))/\(((~ (x = nullval))) -> (exists _alpha_513, self_card = lseg_card_1 _alpha_513))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve lseg_local_factsP : saturate_local.
Definition Gprog : funspecs :=
  ltac:(with_library prog [listcopy_spec; malloc_spec]).

Lemma body_listcopy : semax_body Vprog Gprog f_listcopy listcopy_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename x into x2.
forward.
assert_PROP (is_pointer_or_null x2). { entailer!. }
forward_if.
 - {
    assert_PROP (_alpha_514 = lseg_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
    ssl_card lseg ssl_card_assert .
    assert_PROP ((x2 = nullval)). { entailer!. }
    let ssl_var := fresh in assert_PROP(s = []) as ssl_var; try rewrite ssl_var. { entailer!. }
    forward.
    Exists (lseg_card_0  : lseg_card).
    Exists nullval.
    Exists (lseg_card_0  : lseg_card).
    simpl (lseg nullval [] lseg_card_0) at 1.
    simpl (lseg nullval [] lseg_card_0) at 1.
    entailer!.
}
 - {
     assert_PROP (exists _alpha_513, _alpha_514 = lseg_card_1 _alpha_513) as ssl_card_assert. {
       entailer!; ssl_dispatch_card.
     }
     ssl_card lseg ssl_card_assert _alpha_513x2.
     assert_PROP ((~ (x2 = nullval))). { entailer!. }
     Intros vx2 s1x2 nxtx2.
     let ssl_var := fresh in assert_PROP(s = ([(Vint (Int.repr vx2))] ++ s1x2)) as ssl_var; try rewrite ssl_var. { entailer!. }
     try rename vx2 into vx22.
     forward.
     try rename nxtx2 into nxtx22.
     forward.
     assert_PROP (is_pointer_or_null nxtx22). { entailer!. }
     try rename _alpha_5141 into _alpha_513x2.
     try rename x1 into nxtx22.
     try rename s1 into s1x2.
     try rename r1 into r.
     forward.
     forward_call (r, nxtx22, s1x2, _alpha_513x2).
     let ret := fresh vret in Intros ret; destruct ret as [[_alpha_5161 y1] _alpha_5151].
     try rename y1 into y12.
     forward.
     try rename _alpha_513x21 into _alpha_5151.
     try rename nxtx21 into nxtx22.
     try rename s11x2 into s1x2.
     try rename _alpha_513y into _alpha_5161.
     try rename nxty into y12.
     try rename s11y into s1x2.
     forward_call (tarray (Tunion _sslval noattr) 2).
     Intros y2.
     assert_PROP (isptr y2). { entailer!. }
     forward.
     forward.
     try rename vx21 into vx22.
     forward.
     forward.
     Exists (lseg_card_1 _alpha_5161 : lseg_card).
     Exists y2.
     Exists (lseg_card_1 _alpha_5151 : lseg_card).
     entailer!.
     simpl (lseg _ _ (lseg_card_1 _alpha_5161)) at 1.
     Exists vx22 s1x2 y12.
     simpl (lseg _ _ (lseg_card_1 _alpha_5151)) at 1.
     Exists vx22 s1x2 nxtx22.
     entailer!.
}
Qed.

Lemma body_listcopy_2 : semax_body Vprog Gprog f_listcopy listcopy_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename x into x2.
forward.
assert_PROP (is_pointer_or_null x2). { entailer!. }
forward_if.
 - {
assert_PROP (_alpha_514 = lseg_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card lseg ssl_card_assert .
assert_PROP ((x2 = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = []) as ssl_var; try rewrite ssl_var. { entailer!. }
forward.
Exists (lseg_card_0  : lseg_card).
Exists nullval.
Exists (lseg_card_0  : lseg_card).
entailer!.
simpl (lseg _ _ ((lseg_card_0  : lseg_card))) at 1.
simpl (lseg _ _ ((lseg_card_0  : lseg_card))) at 1.
entailer!.
}
 - {
assert_PROP (exists _alpha_513, _alpha_514 = lseg_card_1 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card lseg ssl_card_assert _alpha_513x2.
assert_PROP ((~ (x2 = nullval))). { entailer!. }
Intros vx2 s1x2 nxtx2.
let ssl_var := fresh in assert_PROP(s = ([(Vint (Int.repr vx2))] ++ s1x2)) as ssl_var; try rewrite ssl_var. { entailer!. }
try rename vx2 into vx22.
forward.
try rename nxtx2 into nxtx22.
forward.
assert_PROP (is_pointer_or_null nxtx22). { entailer!. }
try rename _alpha_5141 into _alpha_513x2.
try rename x1 into nxtx22.
try rename s1 into s1x2.
try rename r1 into r.
forward.
forward_call (r, nxtx22, s1x2, _alpha_513x2).
let ret := fresh vret in Intros ret; destruct ret as [[_alpha_5161 y1] _alpha_5151].
try rename y1 into y12.
forward.
try rename _alpha_513x21 into _alpha_5151.
try rename nxtx21 into nxtx22.
try rename s11x2 into s1x2.
try rename _alpha_513y into _alpha_5161.
try rename nxty into y12.
try rename s11y into s1x2.
forward_call (tarray (Tunion _sslval noattr) 2).
Intros y2.
assert_PROP (isptr y2). { entailer!. }
forward.
forward.
try rename vx21 into vx22.
forward.
forward.
Exists (lseg_card_1 _alpha_5161 : lseg_card).
Exists y2.
Exists (lseg_card_1 _alpha_5151 : lseg_card).
entailer!.
simpl (lseg _ _ ((lseg_card_1 _alpha_5161 : lseg_card))) at 1.
Exists vx22.
Exists s1x2.
Exists y12.
simpl (lseg _ _ ((lseg_card_1 _alpha_5151 : lseg_card))) at 1.
Exists vx22.
Exists s1x2.
Exists nxtx22.
entailer!.
}
Qed.

Lemma body_listcopy3 : semax_body Vprog Gprog f_listcopy listcopy_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename x into x2.
forward.
assert_PROP (is_pointer_or_null x2). { entailer!. }
forward_if.
 - {
assert_PROP (_alpha_514 = lseg_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card lseg ssl_card_assert .
assert_PROP ((x2 = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = []) as ssl_var; try rewrite ssl_var. { entailer!. }
forward.
Exists (lseg_card_0  : lseg_card).
Exists nullval.
Exists (lseg_card_0  : lseg_card).
entailer!.
simpl (lseg _ _ ((lseg_card_0  : lseg_card))) at 1.
simpl (lseg _ _ ((lseg_card_0  : lseg_card))) at 1.
entailer!.

}
 - {
assert_PROP (exists _alpha_513, _alpha_514 = lseg_card_1 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card lseg ssl_card_assert _alpha_513x2.
assert_PROP ((~ (x2 = nullval))). { entailer!. }
Intros vx2 s1x2 nxtx2.
let ssl_var := fresh in assert_PROP(s = ([(Vint (Int.repr vx2))] ++ s1x2)) as ssl_var; try rewrite ssl_var. { entailer!. }
try rename vx2 into vx22.
forward.
try rename nxtx2 into nxtx22.
forward.
assert_PROP (is_pointer_or_null nxtx22). { entailer!. }
try rename _alpha_5141 into _alpha_513x2.
try rename x1 into nxtx22.
try rename s1 into s1x2.
try rename r1 into r.
forward.
forward_call (r, nxtx22, s1x2, _alpha_513x2).
let ret := fresh vret in Intros ret; destruct ret as [[_alpha_5161 y1] _alpha_5151].
try rename y1 into y12.
forward.
try rename _alpha_513x21 into _alpha_5151.
try rename nxtx21 into nxtx22.
try rename s11x2 into s1x2.
try rename _alpha_513y into _alpha_5161.
try rename nxty into y12.
try rename s11y into s1x2.
forward_call (tarray (Tunion _sslval noattr) 2).
Intros y2.
assert_PROP (isptr y2). { entailer!. }
forward.
forward.
try rename vx21 into vx22.
forward.
forward.
Exists (lseg_card_1 _alpha_5161 : lseg_card).
Exists y2.
Exists (lseg_card_1 _alpha_5151 : lseg_card).
entailer!.
simpl (lseg _ _ ((lseg_card_1 _alpha_5161 : lseg_card))) at 1.
Exists vx22.
Exists s1x2.
Exists y12.
simpl (lseg _ _ ((lseg_card_1 _alpha_5151 : lseg_card))) at 1.
Exists vx22.
Exists s1x2.
Exists nxtx22.
entailer!.
}
Qed.



