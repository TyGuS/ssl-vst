
Require Import VST.floyd.proofauto.
Require Import sll_to_dll.
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

Inductive dll_card : Set :=
    | dll_card_0 : dll_card
    | dll_card_1 : dll_card -> dll_card.

Fixpoint dll (x: val) (z: val) (s: (list Z)) (self_card: dll_card) {struct self_card} : mpred := match self_card with
    | dll_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | dll_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list Z),
      EX w : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (w : val)); (inr (z : val))] (x : val)) * (dll (w : val) (x : val) (s1 : list Z) (_alpha_513 : dll_card))
end.

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: val) (s: (list Z)) (self_card: sll_card) {struct self_card} : mpred := match self_card with
    | sll_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | sll_card_1 _alpha_514 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_514 : sll_card))
end.


Definition sll_to_dll_spec :=
  DECLARE _sll_to_dll
   WITH f: val, x: val, s: (list Z), _alpha_515: sll_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((f : val)); is_pointer_or_null((x : val)) )
   PARAMS(f)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x : val))] (f : val)); (sll (x : val) (s : list Z) (_alpha_515 : sll_card)))
   POST[ tvoid ]
   EX i: val,
   EX _alpha_516: dll_card,
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (i : val))] (f : val)); (dll (i : val) nullval (s : list Z) (_alpha_516 : dll_card))).

Lemma dll_x_valid_pointerP x z s self_card: dll x z s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve dll_x_valid_pointerP : valid_pointer.
Lemma dll_z_valid_pointerP x z s self_card: dll x z s self_card |-- valid_pointer z. Proof. Admitted.
Hint Resolve dll_z_valid_pointerP : valid_pointer.
Lemma dll_local_factsP x z s self_card :
  dll x z s self_card|-- !!(((((x : val) = nullval)) -> (self_card = dll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_513, self_card = dll_card_1 _alpha_513))/\(is_pointer_or_null x)/\(is_pointer_or_null z)). Proof. Admitted.
Hint Resolve dll_local_factsP : saturate_local.
Lemma unfold_dll_card_0  (x: val) (z: val) (s: (list Z)) : dll x z s (dll_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_dll_card_1 (_alpha_513 : dll_card) (x: val) (z: val) (s: (list Z)) : dll x z s (dll_card_1 _alpha_513) = 
      EX v : Z,
      EX s1 : (list Z),
      EX w : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (w : val)); (inr (z : val))] (x : val)) * (dll (w : val) (x : val) (s1 : list Z) (_alpha_513 : dll_card)). Proof. auto. Qed.
Lemma sll_x_valid_pointerP x s self_card: sll x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x s self_card :
  sll x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_514, self_card = sll_card_1 _alpha_514))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (s: (list Z)) : sll x s (sll_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_514 : sll_card) (x: val) (s: (list Z)) : sll x s (sll_card_1 _alpha_514) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_514 : sll_card)). Proof. auto. Qed.
Definition Gprog : funspecs :=
  ltac:(with_library prog [sll_to_dll_spec; free_spec; malloc_spec]).

Lemma body_sll_to_dll : semax_body Vprog Gprog f_sll_to_dll sll_to_dll_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr f). { entailer!. }
try rename x into x2.
forward.
forward_if.

 - {
assert_PROP (_alpha_515 = sll_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert .
assert_PROP (((x2 : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists nullval.
Exists (dll_card_0  : dll_card).
try entailer!.
ssl_rewrite_last (unfold_dll_card_0 ).
try entailer!.

}
 - {
assert_PROP (exists _alpha_514, _alpha_515 = sll_card_1 _alpha_514) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert _alpha_514x2.
assert_PROP ((~ ((x2 : val) = nullval))). { entailer!. }
Intros vx2 s1x2 nxtx2.
let ssl_var := fresh in assert_PROP(s = (([(vx2 : Z)] : list Z) ++ (s1x2 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx2 into vx22.
forward.
try rename nxtx2 into nxtx22.
forward.
forward.
assert_PROP(is_pointer_or_null((f : val))). { entailer!. }
assert_PROP(is_pointer_or_null((nxtx22 : val))). { entailer!. }
forward_call ((f : val), (nxtx22 : val), (s1x2 : list Z), (_alpha_514x2 : sll_card)).
let ret := fresh vret in Intros ret; destruct ret as [i1 _alpha_5161].
try rename i1 into i12.
forward.
forward_if.

 - {
assert_PROP (_alpha_5161 = dll_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card dll ssl_card_assert .
assert_PROP (((i12 : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s1x2 = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward_call (tarray (Tunion _sslval noattr) 3).
Intros i2.
assert_PROP (isptr i2). { entailer!. }
forward_call (tarray (Tunion _sslval noattr) 2, x2).
forward.
forward.
forward.
forward.
forward; entailer!.
Exists (i2 : val).
Exists (dll_card_1 (dll_card_0  : dll_card) : dll_card).
try entailer!.
ssl_rewrite_last (unfold_dll_card_1 (dll_card_0  : dll_card)).
Exists (vx22 : Z).
Exists ([] : list Z).
Exists nullval.
try entailer!.
ssl_rewrite_last (unfold_dll_card_0 ).
try entailer!.

}
 - {
assert_PROP (exists _alpha_513, _alpha_5161 = dll_card_1 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card dll ssl_card_assert _alpha_513i12.
assert_PROP ((~ ((i12 : val) = nullval))). { entailer!. }
Intros vi12 s1i12 wi12.
let ssl_var := fresh in assert_PROP(s1x2 = (([(vi12 : Z)] : list Z) ++ (s1i12 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vi12 into vi122.
forward.
try rename wi12 into wi122.
forward.
forward_call (tarray (Tunion _sslval noattr) 3).
Intros i2.
assert_PROP (isptr i2). { entailer!. }
forward_call (tarray (Tunion _sslval noattr) 2, x2).
forward.
forward.
forward.
forward.
forward.
forward.
forward; entailer!.
Exists (i2 : val).
Exists (dll_card_1 (dll_card_1 (_alpha_513i12 : dll_card) : dll_card) : dll_card).
try entailer!.
ssl_rewrite_last (unfold_dll_card_1 (dll_card_1 (_alpha_513i12 : dll_card) : dll_card)).
Exists (vi122 : Z).
Exists (([(vx22 : Z)] : list Z) ++ (s1i12 : list Z)).
Exists (i12 : val).
try entailer!.
ssl_rewrite_last (unfold_dll_card_1 (_alpha_513i12 : dll_card)).
Exists (vx22 : Z).
Exists (s1i12 : list Z).
Exists (wi122 : val).
try entailer!.

}
}
Qed.