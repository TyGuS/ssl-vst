
Require Import VST.floyd.proofauto.
Require Import srtl_insert.
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

Fixpoint sll (x: val) (len: Z) (lo: Z) (hi: Z) (self_card: sll_card) {struct self_card} : mpred := match self_card with
    | sll_card_0  =>  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp
    | sll_card_1 _alpha_513 => 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(Int.min_signed <= len1 <= Int.max_signed) && !!(Int.min_signed <= hi1 <= Int.max_signed) && !!(Int.min_signed <= lo1 <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_513 : sll_card))
end.

Inductive srtl_card : Set :=
    | srtl_card_0 : srtl_card
    | srtl_card_1 : srtl_card -> srtl_card.

Fixpoint srtl (x: val) (len: Z) (lo: Z) (hi: Z) (self_card: srtl_card) {struct self_card} : mpred := match self_card with
    | srtl_card_0  =>  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp
    | srtl_card_1 _alpha_514 => 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(Int.min_signed <= len1 <= Int.max_signed) && !!(Int.min_signed <= hi1 <= Int.max_signed) && !!(Int.min_signed <= lo1 <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && !!((v : Z) <= (lo1 : Z)) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (srtl (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_514 : srtl_card))
end.


Definition srtl_insert_spec :=
  DECLARE _srtl_insert
   WITH x: val, r: val, lo: Z, k: Z, _alpha_515: srtl_card, n: Z, hi: Z
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( (0 <= (k : Z)); (0 <= (n : Z)); ((k : Z) <= 7); is_pointer_or_null((x : val)); is_pointer_or_null((r : val)) )
   PARAMS(x; r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inl ((Vint (Int.repr k)) : val))] (r : val)); (srtl (x : val) (n : Z) (lo : Z) (hi : Z) (_alpha_515 : srtl_card)))
   POST[ tvoid ]
   EX n1: Z,
   EX y: val,
   EX hi1: Z,
   EX _alpha_516: srtl_card,
   EX lo1: Z,
   PROP( ((hi1 : Z) = (if (Z.leb (hi : Z) (k : Z)) then (k : Z) else (hi : Z))); ((lo1 : Z) = (if (Z.leb (k : Z) (lo : Z)) then (k : Z) else (lo : Z))); ((n1 : Z) = ((n : Z) + 1)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (r : val)); (srtl (y : val) (n1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_516 : srtl_card))).

Lemma sll_x_valid_pointerP x len lo hi self_card: sll x len lo hi self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x len lo hi self_card :
  sll x len lo hi self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_513, self_card = sll_card_1 _alpha_513))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (len: Z) (lo: Z) (hi: Z) : sll x len lo hi (sll_card_0 ) =  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_513 : sll_card) (x: val) (len: Z) (lo: Z) (hi: Z) : sll x len lo hi (sll_card_1 _alpha_513) = 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(Int.min_signed <= len1 <= Int.max_signed) && !!(Int.min_signed <= hi1 <= Int.max_signed) && !!(Int.min_signed <= lo1 <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_513 : sll_card)). Proof. auto. Qed.
Lemma srtl_x_valid_pointerP x len lo hi self_card: srtl x len lo hi self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve srtl_x_valid_pointerP : valid_pointer.
Lemma srtl_local_factsP x len lo hi self_card :
  srtl x len lo hi self_card|-- !!(((((x : val) = nullval)) -> (self_card = srtl_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_514, self_card = srtl_card_1 _alpha_514))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve srtl_local_factsP : saturate_local.
Lemma unfold_srtl_card_0  (x: val) (len: Z) (lo: Z) (hi: Z) : srtl x len lo hi (srtl_card_0 ) =  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp. Proof. auto. Qed.
Lemma unfold_srtl_card_1 (_alpha_514 : srtl_card) (x: val) (len: Z) (lo: Z) (hi: Z) : srtl x len lo hi (srtl_card_1 _alpha_514) = 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(Int.min_signed <= len1 <= Int.max_signed) && !!(Int.min_signed <= hi1 <= Int.max_signed) && !!(Int.min_signed <= lo1 <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && !!((v : Z) <= (lo1 : Z)) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (srtl (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_514 : srtl_card)). Proof. auto. Qed.
Definition Gprog : funspecs :=
  ltac:(with_library prog [srtl_insert_spec; malloc_spec]).

Lemma body_srtl_insert : semax_body Vprog Gprog f_srtl_insert srtl_insert_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename k into k2.
forward.
forward_if.

 - {
assert_PROP (_alpha_515 = srtl_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card srtl ssl_card_assert .
assert_PROP (((x : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(hi = 0) as ssl_var; try rewrite ssl_var in *. { entailer!. }
let ssl_var := fresh in assert_PROP(lo = 7) as ssl_var; try rewrite ssl_var in *. { entailer!. }
let ssl_var := fresh in assert_PROP(n = 0) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward_call (tarray (Tunion _sslval noattr) 2).
Intros y2.
assert_PROP (isptr y2). { entailer!. }
forward.
forward.
forward.
forward; entailer!.
Exists (0 + 1).
Exists (y2 : val).
Exists (if (Z.leb 0 (k2 : Z)) then (k2 : Z) else 0).
Exists (srtl_card_1 (srtl_card_0  : srtl_card) : srtl_card).
Exists (if (Z.leb (k2 : Z) 7) then (k2 : Z) else 7).
try entailer!.
ssl_rewrite_last (unfold_srtl_card_1 (srtl_card_0  : srtl_card)).
Exists (k2 : Z).
Exists nullval.
Exists 0.
Exists 0.
Exists 7.
try entailer!.
ssl_rewrite_last (unfold_srtl_card_0 ).
try entailer!.

}
 - {
assert_PROP (exists _alpha_514, _alpha_515 = srtl_card_1 _alpha_514) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card srtl ssl_card_assert _alpha_514x.
assert_PROP ((~ ((x : val) = nullval))). { entailer!. }
Intros vx nxtx len1x hi1x lo1x.
let ssl_var := fresh in assert_PROP(hi = (if (Z.leb (hi1x : Z) (vx : Z)) then (vx : Z) else (hi1x : Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
let ssl_var := fresh in assert_PROP(lo = (if (Z.leb (vx : Z) (lo1x : Z)) then (vx : Z) else (lo1x : Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
let ssl_var := fresh in assert_PROP(n = (1 + (len1x : Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx into vx2.
forward.
forward_if.

 - {
try rename nxtx into nxtx2.
forward.
forward_call (tarray (Tunion _sslval noattr) 2).
Intros nxty2.
assert_PROP (isptr nxty2). { entailer!. }
forward.
forward.
forward.
forward.
forward; entailer!.
Exists ((1 + (len1x : Z)) + 1).
Exists (x : val).
Exists (if (Z.leb (if (Z.leb (hi1x : Z) (vx2 : Z)) then (vx2 : Z) else (hi1x : Z)) (k2 : Z)) then (k2 : Z) else (if (Z.leb (hi1x : Z) (vx2 : Z)) then (vx2 : Z) else (hi1x : Z))).
Exists (srtl_card_1 (srtl_card_1 (_alpha_514x : srtl_card) : srtl_card) : srtl_card).
Exists (if (Z.leb (k2 : Z) (if (Z.leb (vx2 : Z) (lo1x : Z)) then (vx2 : Z) else (lo1x : Z))) then (k2 : Z) else (if (Z.leb (vx2 : Z) (lo1x : Z)) then (vx2 : Z) else (lo1x : Z))).
try entailer!.
ssl_rewrite_last (unfold_srtl_card_1 (srtl_card_1 (_alpha_514x : srtl_card) : srtl_card)).
Exists (vx2 : Z).
Exists (nxty2 : val).
Exists (1 + (len1x : Z)).
Exists (if (Z.leb (hi1x : Z) (k2 : Z)) then (k2 : Z) else (hi1x : Z)).
Exists (if (Z.leb (k2 : Z) (lo1x : Z)) then (k2 : Z) else (lo1x : Z)).
try entailer!.
ssl_rewrite_last (unfold_srtl_card_1 (_alpha_514x : srtl_card)).
Exists (k2 : Z).
Exists (nxtx2 : val).
Exists (len1x : Z).
Exists (hi1x : Z).
Exists (lo1x : Z).
try entailer!.

}
 - {
forward_if.

 - {
try rename nxtx into nxtx2.
forward.
assert_PROP((0 <= (k2 : Z))). { entailer!. }
assert_PROP((0 <= (len1x : Z))). { entailer!. }
assert_PROP(((k2 : Z) <= 7)). { entailer!. }
assert_PROP(is_pointer_or_null((nxtx2 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((r : val))). { entailer!. }
forward_call ((nxtx2 : val), (r : val), (lo1x : Z), (k2 : Z), (_alpha_514x : srtl_card), (len1x : Z), (hi1x : Z)).
let ret := fresh vret in Intros ret; destruct ret as [[[[n11 y1] hi11] _alpha_5161] lo11].
let ssl_var := fresh in assert_PROP(hi11 = (if (Z.leb (hi1x : Z) (k2 : Z)) then (k2 : Z) else (hi1x : Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
let ssl_var := fresh in assert_PROP(lo11 = (if (Z.leb (k2 : Z) (lo1x : Z)) then (k2 : Z) else (lo1x : Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
let ssl_var := fresh in assert_PROP(n11 = ((len1x : Z) + 1)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename y1 into y12.
forward.
forward.
forward.
forward; entailer!.
Exists ((1 + (len1x : Z)) + 1).
Exists (x : val).
Exists (if (Z.leb (if (Z.leb (hi1x : Z) (vx2 : Z)) then (vx2 : Z) else (hi1x : Z)) (k2 : Z)) then (k2 : Z) else (if (Z.leb (hi1x : Z) (vx2 : Z)) then (vx2 : Z) else (hi1x : Z))).
Exists (srtl_card_1 (_alpha_5161 : srtl_card) : srtl_card).
Exists (if (Z.leb (k2 : Z) (if (Z.leb (vx2 : Z) (lo1x : Z)) then (vx2 : Z) else (lo1x : Z))) then (k2 : Z) else (if (Z.leb (vx2 : Z) (lo1x : Z)) then (vx2 : Z) else (lo1x : Z))).
try entailer!.
ssl_rewrite_last (unfold_srtl_card_1 (_alpha_5161 : srtl_card)).
Exists (vx2 : Z).
Exists (y12 : val).
Exists ((len1x : Z) + 1).
Exists (if (Z.leb (hi1x : Z) (k2 : Z)) then (k2 : Z) else (hi1x : Z)).
Exists (if (Z.leb (k2 : Z) (lo1x : Z)) then (k2 : Z) else (lo1x : Z)).
try entailer!.

}
 - {
try rename nxtx into nxtx2.
forward.
forward_call (tarray (Tunion _sslval noattr) 2).
Intros nxty2.
assert_PROP (isptr nxty2). { entailer!. }
forward.
forward.
forward.
forward.
forward.
forward; entailer!.
Exists ((1 + (len1x : Z)) + 1).
Exists (x : val).
Exists (if (Z.leb (if (Z.leb (hi1x : Z) (vx2 : Z)) then (vx2 : Z) else (hi1x : Z)) (k2 : Z)) then (k2 : Z) else (if (Z.leb (hi1x : Z) (vx2 : Z)) then (vx2 : Z) else (hi1x : Z))).
Exists (srtl_card_1 (srtl_card_1 (_alpha_514x : srtl_card) : srtl_card) : srtl_card).
Exists (if (Z.leb (k2 : Z) (if (Z.leb (vx2 : Z) (lo1x : Z)) then (vx2 : Z) else (lo1x : Z))) then (k2 : Z) else (if (Z.leb (vx2 : Z) (lo1x : Z)) then (vx2 : Z) else (lo1x : Z))).
try entailer!.
ssl_rewrite_last (unfold_srtl_card_1 (srtl_card_1 (_alpha_514x : srtl_card) : srtl_card)).
Exists (k2 : Z).
Exists (nxty2 : val).
Exists (1 + (len1x : Z)).
Exists (if (Z.leb (hi1x : Z) (vx2 : Z)) then (vx2 : Z) else (hi1x : Z)).
Exists (if (Z.leb (vx2 : Z) (lo1x : Z)) then (vx2 : Z) else (lo1x : Z)).
try entailer!.
ssl_rewrite_last (unfold_srtl_card_1 (_alpha_514x : srtl_card)).
Exists (vx2 : Z).
Exists (nxtx2 : val).
Exists (len1x : Z).
Exists (hi1x : Z).
Exists (lo1x : Z).
try entailer!.

}
}
}
Qed.