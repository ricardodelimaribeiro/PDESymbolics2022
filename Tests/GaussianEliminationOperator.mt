(* Wolfram Language Test file *)
	test = "Tests/GaussianEliminationOperatorChild.mt";
        Print["   GaussianEliminationOperator"];
(*variables = Association[
    "expression" -> $Failed, 
    "result" -> $Failed
    ];

label = "$Failed"
Get[ test ]
*)
    label = "Identity";
    system = Association[{
        "matrix" -> {{1,0}, {0, 1}},
        "vector" -> {1, 1}, 
        "result"->Association[{"matrix" -> {{1, 0}, {0, 1}}, "vector" -> {1, 1}}]
    }];
    field = Association[{
        "generators" -> {},
        "facts"->True,
        "pars" -> {}
    }];
    Get[ test ]
    
    label = "one third";
    system =
  	Association[{
    	"matrix" -> {{1, 2}, {2, 1}},
    	"vector" -> {1, 1},
    	"result" -> <|"matrix" -> {{1, 0}, {0, 1}}, "vector" -> {1/3, 1/3}|>
    }];
    field =
  	Association[{
    	"generators" -> {},
    	"facts"->True,
    	"pars" -> {}
    }];
    Get[ test ]
    
    label = "polinomial with parameter";
    system =
  	Association[{
    	"matrix" -> {{x, x^2}, {a x + a, a x}},
    	"vector" -> {1, a^2},
    	"depVars"->{},
    	"indVars"->{},
    	"result" -> Piecewise[{{<|"matrix" -> {{1, 0}, {0, 1}}, "vector" -> {x^(-1) - (1 + x - a*x)/x^2, (1 + x - a*x)/x^3}|>, a != 0}, {<|"matrix" -> {{1, x}}, "vector" -> {x^(-1)}|>, a == 0}}, $Failed]
    }];
    field =
  	Association[{
    	"generators" -> {x},
    	"depVars"->{},
    	"indVars"->{},
    	"pars" -> {a}
    }];
    Get[ test ]
    
    label = "polinomial with parameter and facts (formerly known as condition)";
    (*had to move result outside of system...*)
    result = Piecewise[{{<|"matrix" -> {{1, 0}, {0, 1}}, "vector" -> {x^(-1) - (1 + x - a*x)/x^2, (1 + x - a*x)/x^3}|>, a < 3 && a != 0}, {<|"matrix" -> {{1, x}}, "vector" -> {x^(-1)}|>, a == 0}}, $Failed];
    system =
  	Association[{
    	"matrix" -> {{x, x^2}, {a x + a, a x}},
    	"vector" -> {1, a^2}
    	(*,"result" -> Piecewise[{{<|"matrix" -> {{1, 0}, {0, 1}}, "vector" -> {x^(-1) - (1 + x - a*x)/x^2, (1 + x - a*x)/x^3}|>, a < 3 && a != 0}, {<|"matrix" -> {{1, x}}, "vector" -> {x^(-1)}|>, a == 0}}, $Failed]*)
    }];
    field =
  	Association[{
    	"generators" -> {x},
    	"pars" -> {a},
    	"facts" -> a<3
    }];
    Get [ test ]

    label = "inverse"
    system =
  	Association[
    	"matrix" -> {{x, x^2}, {a x + a, a x}},
    	"vector" -> IdentityMatrix[2]
    	,"result" -> Piecewise[{{<|"matrix" -> {{1, 0}, {0, 1}}, "vector" -> {{x^(-1) - (1 + x)/x^2, 1/(a*x)}, {(1 + x)/x^3, -(1/(a*x^2))}}|>, a != 0}}, $Failed]
    ];
	field =
  	Association[{
    	"generators" -> {x},
    	"pars" -> {a}
    }];
    Get[ test ]