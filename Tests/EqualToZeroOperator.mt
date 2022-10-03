(* Wolfram Language Test file *)
test = "Tests/EqualToZeroOperatorChild.mt";
		Print["   EqualToZeroOperator"];

TestEqualToZero[variables_, xp_] := 
And @@ FullSimplify[# == (0 & /@ #) & /@ (xp /. (EqualToZeroOperator[variables][xp])[[All, 1]])]

TestEqualToZeroSA[variables_, xp_] :=
 With[
  {vrs = Complement[Variables[xp], variables["pars"]],
   pars = variables["pars"]},
  Union[(pars /. SolveAlways[(# == 0 & /@ Flatten[{xp}]), vrs])] === 
   Union[(pars /. ((EqualToZeroOperator[variables][xp])[[All, 1]]))]  
  ]

variables = Association[
	"expression" -> $Failed, 
	"result" -> $Failed
	];

label = "$Failed"
Get[ test ]

    variables = Association[{
        "depVars" -> {u},
        "indVars" -> {n},
        "expression" -> (u[n+1]-u[n])^2 + u[n]^2,
        "result" -> False
    }];
    label = "Mechanics"    
    Get[ test ]