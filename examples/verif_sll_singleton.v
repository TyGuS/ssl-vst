
Require Import VST.floyd.proofauto.
Require Import sll_singleton.
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


Definition sll_singleton_spec :=
  DECLARE _sll_singleton
   WITH x: val, p: val, a: val
   PRE [ tint, (tptr (Tunion _sslval noattr)) ]
   PROP( ssl_is_valid_int((x : val)); is_pointer_or_null((p : val)); is_pointer_or_null((a : val)) )
   PARAMS(x; p)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (a : val))] (p : val)))
   POST[ tvoid ]
   EX y: val,
   EX elems: (list Z),
   EX _alpha_514: sll_card,
   PROP( ((elems : list Z) = ([(force_signed_int (x : val))] : list Z)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (p : val)); (sll (y : val) (elems : list Z) (_alpha_514 : sll_card))).

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
  ltac:(with_library prog [sll_singleton_spec; malloc_spec]).

Lemma body_sll_singleton : semax_body Vprog Gprog f_sll_singleton sll_singleton_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr p). { entailer!. }
try rename a into a2.
forward.
forward_call (tarray (Tunion _sslval noattr) 2).
Intros y2.
assert_PROP (isptr y2). { entailer!. }
forward.
forward.
forward.
forward; entailer!.
Exists (y2 : val).
Exists ([(x : Z)] : list Z).
Exists (sll_card_1 (sll_card_0  : sll_card) : sll_card).
ssl_entailer.
ssl_rewrite_last (unfold_sll_card_1 (sll_card_0  : sll_card)).
Exists (x : Z).
Exists ([] : list Z).
Exists nullval.
ssl_entailer.
ssl_rewrite_last (unfold_sll_card_0 ).
ssl_entailer.

Qed.