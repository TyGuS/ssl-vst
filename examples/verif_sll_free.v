
Require Import VST.floyd.proofauto.
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


Definition sll_free_spec :=
  DECLARE _sll_free
   WITH x: val, s: (list Z), _alpha_514: sll_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x : val)) )
   PARAMS(x)
   SEP ((sll (x : val) (s : list Z) (_alpha_514 : sll_card)))
   POST[ tvoid ]
   PROP(  )
   LOCAL()
   SEP ().

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
  ltac:(with_library prog [sll_free_spec; free_spec]).

Lemma body_sll_free : semax_body Vprog Gprog f_sll_free sll_free_spec.
Proof.
start_function.
ssl_open_context.
forward_if.

 - {
assert_PROP (_alpha_514 = sll_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert .
assert_PROP (((x : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.

}
 - {
assert_PROP (exists _alpha_513, _alpha_514 = sll_card_1 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert _alpha_513x.
assert_PROP ((~ ((x : val) = nullval))). { entailer!. }
Intros vx s1x nxtx.
let ssl_var := fresh in assert_PROP(s = (([(vx : Z)] : list Z) ++ (s1x : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx into vx2.
forward.
try rename nxtx into nxtx2.
forward.
assert_PROP(is_pointer_or_null((nxtx2 : val))). { entailer!. }
forward_call ((nxtx2 : val), (s1x : list Z), (_alpha_513x : sll_card)).
forward_call (tarray (Tunion _sslval noattr) 2, x).
forward; entailer!.

}
Qed.