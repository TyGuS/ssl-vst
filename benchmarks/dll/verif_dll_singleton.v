
Require Import VST.floyd.proofauto.
Require Import common_predicates.
Require Import dll_singleton.
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









Definition dll_singleton_spec :=
  DECLARE _dll_singleton
   WITH x: val, r: val, a: val
   PRE [ tint, (tptr (Tunion _sslval noattr)) ]
   PROP( ssl_is_valid_int((x : val)); is_pointer_or_null((r : val)); is_pointer_or_null((a : val)) )
   PARAMS(x; r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (a : val))] (r : val)))
   POST[ tvoid ]
   EX y: val,
   EX elems: (list Z),
   EX _alpha_534: dll_card,
   PROP( ((elems : list Z) = ([(force_signed_int (x : val))] : list Z)); is_pointer_or_null((y : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (r : val)); (dll (y : val) nullval (elems : list Z) (_alpha_534 : dll_card))).






Definition Gprog : funspecs :=
  ltac:(with_library prog [dll_singleton_spec; malloc_spec]).


Lemma body_dll_singleton : semax_body Vprog Gprog f_dll_singleton dll_singleton_spec.
Proof.

start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename a into a2.
forward.
forward_call (tarray (Tunion _sslval noattr) 3).
Intros y2.
assert_PROP (isptr y2). { entailer!. }
forward.
forward.
forward.
forward.
forward; entailer!.
Exists (y2 : val).
Exists ([(x : Z)] : list Z).
Exists (dll_card_1 (dll_card_0  : dll_card) : dll_card).
ssl_entailer.
rewrite (unfold_dll_card_1 (dll_card_0  : dll_card)) at 1.
Exists (x : Z).
Exists ([] : list Z).
Exists nullval.
ssl_entailer.
rewrite (unfold_dll_card_0 ) at 1.
ssl_entailer.


Qed.