
Require Import VST.floyd.proofauto.
Require Import mk_acc.
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

Inductive account_card : Set :=
    | account_card_0 : account_card.

Fixpoint account (x: val) (id: Z) (bal: Z) (self_card: account_card) {struct self_card} : mpred := match self_card with
    | account_card_0  =>  !!(is_true true) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr id)) : val)); (inl ((Vint (Int.repr bal)) : val))] (x : val))
end.


Definition mk_acc_spec :=
  DECLARE _mk_acc
   WITH r: val, id: val, bal: Z
   PRE [ (tptr (Tunion _sslval noattr)), tint ]
   PROP( is_pointer_or_null((r : val)); ssl_is_valid_int((id : val)) )
   PARAMS(r; id)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inl ((Vint (Int.repr bal)) : val))] (r : val)))
   POST[ tvoid ]
   EX x: val,
   EX _alpha_513: account_card,
   PROP( is_pointer_or_null((x : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x : val))] (r : val)); (account (x : val) (force_signed_int (id : val)) (bal : Z) (_alpha_513 : account_card))).

Lemma account_x_valid_pointerP x id bal self_card: account x id bal self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve account_x_valid_pointerP : valid_pointer.
Lemma account_local_factsP x id bal self_card :
  account x id bal self_card|-- !!((((is_true true)) -> (self_card = account_card_0))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve account_local_factsP : saturate_local.
Lemma unfold_account_card_0  (x: val) (id: Z) (bal: Z) : account x id bal (account_card_0 ) =  !!(is_true true) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr id)) : val)); (inl ((Vint (Int.repr bal)) : val))] (x : val)). Proof. auto. Qed.
Definition Gprog : funspecs :=
  ltac:(with_library prog [mk_acc_spec; malloc_spec]).

Lemma body_mk_acc : semax_body Vprog Gprog f_mk_acc mk_acc_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename bal into bal2.
forward.
forward_call (tarray (Tunion _sslval noattr) 2).
Intros x2.
assert_PROP (isptr x2). { entailer!. }
forward.
forward.
forward.
forward; entailer!.
Exists (x2 : val).
Exists (account_card_0  : account_card).
ssl_entailer.
rewrite (unfold_account_card_0 ) at 1.
ssl_entailer.

Qed.