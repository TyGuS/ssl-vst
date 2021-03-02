
Require Import VST.floyd.proofauto.
Require Import common_predicates.
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
   EX _alpha_532: sll_card,
   PROP( ((elems : list Z) = ([(force_signed_int (x : val))] : list Z)); is_pointer_or_null((y : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (p : val)); (sll (y : val) (elems : list Z) (_alpha_532 : sll_card))).






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
rewrite (unfold_sll_card_1 (sll_card_0  : sll_card)) at 1.
Exists (x : Z).
Exists ([] : list Z).
Exists nullval.
ssl_entailer.
rewrite (unfold_sll_card_0 ) at 1.
ssl_entailer.


Qed.