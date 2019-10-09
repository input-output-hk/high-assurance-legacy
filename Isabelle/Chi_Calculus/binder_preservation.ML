(*  Title:      Chi_Calculus/binder_preservation.ML
    Author:     Wolfgang Jeltsch, Well-Typed LLP

Further variants of Syntax_Trans.preserve_binder_abs_tr' from Pure/Syntax/syntax_trans.ML.
*)

(* Constructs like Receive *)

fun preserve_binder_abs_receive_tr' name syn = (name, fn _ => fn A :: Abs abs :: ts =>
  let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
  in list_comb (Syntax.const syn $ A $ x $ t, ts) end);

(* Constructs like general_parallel *)

fun preserve_binder_abs_general_parallel_tr' name syn = (name, fn _ => fn Abs abs :: A :: ts =>
  let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
  in list_comb (Syntax.const syn $ x $ A $ t, ts) end);
