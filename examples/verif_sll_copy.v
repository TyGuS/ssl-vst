
Require Import VST.floyd.proofauto.
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

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: val) (s: (list Z)) (self_card: sll_card) {struct self_card} : mpred := match self_card with
    | sll_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | sll_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_513 : sll_card))
end.


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
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (r : val)); (sll (y : val) (s : list Z) (b : sll_card)); (sll (x : val) (s : list Z) (a : sll_card))).

Lemma sll_x_valid_pointerP x s self_card: sll x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x s self_card :
  sll x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_513, self_card = sll_card_1 _alpha_513))/\is_pointer_or_null((x : val))). Proof. Admitted.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (s: (list Z)) : sll x s (sll_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_513 : sll_card) (x: val) (s: (list Z)) : sll x s (sll_card_1 _alpha_513) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_513 : sll_card)). Proof. auto. Qed.
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
ssl_rewrite_last (unfold_sll_card_0 ).
ssl_entailer.
ssl_rewrite_last (unfold_sll_card_0 ).
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_513, a = sll_card_1 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert _alpha_513x2.
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
forward_call ((r : val), (nxtx22 : val), (s1x2 : list Z), (_alpha_513x2 : sll_card)).
let ret := fresh vret in Intros ret; destruct ret as [y1 b1].
assert_PROP(is_pointer_or_null((y1 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((nxtx22 : val))). { entailer!. }
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
ssl_rewrite_last (unfold_sll_card_1 (_alpha_513x2 : sll_card)).
Exists (vx22 : Z).
Exists (s1x2 : list Z).
Exists (nxtx22 : val).
ssl_entailer.
ssl_rewrite_last (unfold_sll_card_1 (b1 : sll_card)).
Exists (vx22 : Z).
Exists (s1x2 : list Z).
Exists (y12 : val).
ssl_entailer.

}
Qed.