
type info = string

datatype term =
         TmTrue of info
         | TmFalse of info
         | TmIf of info * term * term * term
         | TmZero of info
         | TmSucc of info * term
         | TmPred of info * term
         | TmIsZero of info * term

fun isNumericVal (TmZero _) = true
  | isNumericVal (TmSucc (_, t1)) = isNumericVal t1
  | isNumericVal _ = false

fun isVal (TmTrue _) = true
  | isVal (TmFalse _) = true
  | isVal t = isNumericVal t

fun evalBig (TmIf (_, t1, t2, t3)): term option =
    Option.mapPartial (fn t1' => (case (t1') of
                                      TmTrue _ => Option.mapPartial (fn v2 => if isVal v2 then SOME v2 else NONE) (evalBig t2)
                                    | TmFalse _ => Option.mapPartial (fn v3 => if isVal v3 then SOME v3 else NONE) (evalBig t3)
                                    | _ => NONE)) (evalBig t1)
  | evalBig (TmSucc (fi, t1)) = Option.mapPartial (fn nv1 => if isNumericVal nv1 then SOME (TmSucc (fi, nv1)) else NONE) (evalBig t1)
  | evalBig (TmPred (fi, t1)) = Option.mapPartial (fn t1' =>
                                                      (case t1' of
                                                           (TmZero fi) => SOME (TmZero fi)
                                                         | (TmSucc (fi, nv1)) => if isNumericVal nv1 then SOME nv1 else NONE
                                                  )) (evalBig t1)
  | evalBig (TmIsZero (fi, t1)) = Option.mapPartial (fn t1' =>
                                                        (case t1' of
                                                             (TmZero fi) => SOME (TmTrue fi)
                                                           | (TmSucc (fi, nv1)) => if isNumericVal nv1 then SOME (TmFalse fi) else NONE
                                                           | _ => NONE))
                                                    (evalBig t1)
  | evalBig v = if isVal v then SOME v else NONE

fun eval1 (TmIf (_, TmTrue _, t2, t3): term): term option = SOME t2
  | eval1 (TmIf (_, TmFalse _, t2, t3)) = SOME t3
  | eval1 (TmIf (fi, t1, t2, t3)) = Option.mapPartial (fn t1' => SOME (TmIf (fi, t1', t2, t3))) (eval1 t1)
  | eval1 (TmSucc (fi, t1)) = Option.mapPartial (fn t1' => SOME (TmSucc (fi, t1'))) (eval1 t1)
  | eval1 (TmPred (fi, TmZero _)) = SOME (TmZero fi)
  | eval1 (TmPred (_, TmSucc (_, nv1))) = if isNumericVal nv1 then SOME (nv1) else NONE
  | eval1 (TmPred (fi, t1)) = Option.mapPartial (fn t1' => SOME (TmPred (fi, t1'))) (eval1 t1)
  | eval1 (TmIsZero (_, TmZero fi)) = SOME (TmTrue fi)
  | eval1 (TmIsZero (_, TmSucc (fi, nv1))) = if isNumericVal nv1 then SOME (TmFalse fi) else NONE
  | eval1 (TmIsZero (fi, t1)) = Option.mapPartial (fn t1' => SOME (TmPred (fi, t1'))) (eval1 t1)
  | eval1 _ = NONE

exception NoRuleApplies

fun eval t =
    (case (eval1 t) of
         SOME r => eval r
       | NONE => t)


