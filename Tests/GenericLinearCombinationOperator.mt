(* Wolfram Language Test file *)
	test = "Tests/GenericLinearCombinationOperatorChild.mt";
        Print["   GenericLinearCombinationOperator"];
        
        
label = "$Failed"
options = <|"result"->$Failed|>;
list = $Failed
Get[test]

label = "list with 2"
options = <|"result"->{Subscript[\[FormalA], 1] u[x] + 
  Subscript[\[FormalA], 2] Derivative[1][u][x], {Subscript[\[FormalA],
   1], Subscript[\[FormalA], 2]}}|>;
list = {u[x], u'[x]};
Get[test]

label = "coeff is FormalC"
options = <|"coeff" -> \[FormalC], "result"->{Subscript[\[FormalC], 1] u[x] + 
  Subscript[\[FormalC], 2] Derivative[1][u][x], {Subscript[\[FormalC],
   1], Subscript[\[FormalC], 2]}}|>;
list = {u[x], u'[x]};
Get[test]

label = "unique is true"
options = <|"unique"->True, "result"->{Subscript[\[FormalA], 1] u[x] + 
  Subscript[\[FormalA], 2] Derivative[1][u][x], {Subscript[\[FormalA],
   1], Subscript[\[FormalA], 2]}}|>;
list = {u[x], u'[x]};
Get[test]


