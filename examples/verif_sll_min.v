
Require Import VST.floyd.proofauto.
Require Import sll_min.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(Int.min_signed <= len1 <= Int.max_signed) && !!(Int.min_signed <= hi1 <= Int.max_signed) && !!(Int.min_signed <= lo1 <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_513 : sll_card))
end.


Definition sll_min_spec :=
  DECLARE _sll_min
   WITH x: val, r: val, lo: Z, a: val, n: Z, _alpha_514: sll_card, hi: Z
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x : val)); is_pointer_or_null((r : val)); is_pointer_or_null((a : val)) )
   PARAMS(x; r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (a : val))] (r : val)); (sll (x : val) (n : Z) (lo : Z) (hi : Z) (_alpha_514 : sll_card)))
   POST[ tvoid ]
   EX _alpha_515: sll_card,
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inl ((Vint (Int.repr lo)) : val))] (r : val)); (sll (x : val) (n : Z) (lo : Z) (hi : Z) (_alpha_515 : sll_card))).

Lemma sll_x_valid_pointerP x len lo hi self_card: sll x len lo hi self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x len lo hi self_card :
  sll x len lo hi self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_513, self_card = sll_card_1 _alpha_513))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (len: Z) (lo: Z) (hi: Z) : sll x len lo hi (sll_card_0 ) =  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_513 : sll_card) (x: val) (len: Z) (lo: Z) (hi: Z) : sll x len lo hi (sll_card_1 _alpha_513) = 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(Int.min_signed <= len1 <= Int.max_signed) && !!(Int.min_signed <= hi1 <= Int.max_signed) && !!(Int.min_signed <= lo1 <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_513 : sll_card)). Proof. auto. Qed.
Definition Gprog : funspecs :=
  ltac:(with_library prog [sll_min_spec]).

Lemma body_sll_min : semax_body Vprog Gprog f_sll_min sll_min_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename a into a2.
forward.
forward_if.

 - {
assert_PROP (_alpha_514 = sll_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert .
assert_PROP (((x : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(hi = 0) as ssl_var; try rewrite ssl_var in *. { entailer!. }
let ssl_var := fresh in assert_PROP(lo = 7) as ssl_var; try rewrite ssl_var in *. { entailer!. }
let ssl_var := fresh in assert_PROP(n = 0) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward.
forward; entailer!.
Exists (sll_card_0  : sll_card).
ssl_entailer.
rewrite (unfold_sll_card_0 ) at 1.
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_513, _alpha_514 = sll_card_1 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert _alpha_513x.
assert_PROP ((~ ((x : val) = nullval))). { entailer!. }
Intros vx nxtx len1x hi1x lo1x.
let ssl_var := fresh in assert_PROP(hi = (if (Z.leb (hi1x : Z) (vx : Z)) then (vx : Z) else (hi1x : Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
let ssl_var := fresh in assert_PROP(lo = (if (Z.leb (vx : Z) (lo1x : Z)) then (vx : Z) else (lo1x : Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
let ssl_var := fresh in assert_PROP(n = (1 + (len1x : Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx into vx2.
forward.
try rename nxtx into nxtx2.
forward.
assert_PROP(is_pointer_or_null((nxtx2 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((r : val))). { entailer!. }
assert_PROP(is_pointer_or_null((a2 : val))). { entailer!. }
forward_call ((nxtx2 : val), (r : val), (lo1x : Z), (a2 : val), (len1x : Z), (_alpha_513x : sll_card), (hi1x : Z)).
Intros _alpha_5151.
assert_PROP(is_pointer_or_null((nxtx2 : val))). { entailer!. }
try rename lo1x into lo1x2.
forward.
ssl_forward_write_ternary (((Vint (Int.repr ((if (Z.leb (vx2 : Z) (lo1x2 : Z)) then (vx2 : Z) else (lo1x2 : Z))))) : val));
try (forward; entailer!; ssl_reflect_boolean).
forward.
forward; entailer!.
Exists (sll_card_1 (_alpha_5151 : sll_card) : sll_card).
ssl_entailer.
rewrite (unfold_sll_card_1 (_alpha_5151 : sll_card)) at 1.
Exists (vx2 : Z).
Exists (nxtx2 : val).
Exists (len1x : Z).
Exists (hi1x : Z).
Exists (lo1x2 : Z).
ssl_entailer.

}
Qed.