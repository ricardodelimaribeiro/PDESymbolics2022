(* Wolfram Language Test file *)
test = "Tests/ImprovedHomogeneousSolveAlwaysOperatorChild.mt";
		Print["   ImprovedHomogeneousSolveAlwaysOperator"];

label = "$Failed"
variables = Association[
	"expression" -> $Failed, 
	"result" -> $Failed
	];
Get[ test ]

label = "singular"
variables = Association[
	"generators" -> {x}, 
	"pars" -> {a, b, c},
	"expression" -> a + c/x - b/x^2 == 0,
	"result" -> {{{c -> 0, b -> 0, a -> 0}, c == 0 && b == 0 && a == 0}}
	];
Get[test]

label = "non-expandable"
variables = Association[
	"generators" -> {x}, 
	"pars" -> {a, b, c},
	"expression" -> (a x + b)^c == 0,
	"result" -> {{{a -> 0, b -> 0}, a == 0 && b == 0 && c > 0}}
	];
Get[test]

label = "Exponential"
variables = Association[
	"generators" -> {x}, 
	"pars" -> {a, b},
	"expression" -> {E^(a  x) (b x + a^2 x) == 0},
	"result" -> {{{a -> (-I)*Sqrt[b]}, a == (-I)*Sqrt[b]}, {{a -> I*Sqrt[b]}, a == I*Sqrt[b]}}
	];
Get[test]

label = "Exponential with extra power"
variables = Association[
	"generators" -> {x}, 
	"pars" -> {a, b, c},
	"expression" -> E^(a  x) (b x + a^2 x) (a x + b + 1)^c == 0,
	"result" -> {{{a -> 0, b -> -1}, a == 0 && b == -1 && c > 0}, {{a -> (-I)*Sqrt[b]}, a == (-I)*Sqrt[b]}, {{a -> I*Sqrt[b]}, a == I*Sqrt[b]}}
	];
Get[test]

label = "almost linear system"
variables = Association[
	"generators" -> {x,y}, 
	"pars" -> {a, b},
	"expression" -> (a^2 - 4) x == 0 && (b^2 - a) x  y == 0,
	"result" -> {{{a -> -2, b -> (-I)*Sqrt[2]}, a == -2 && b == (-I)*Sqrt[2]}, {{a -> -2, b -> I*Sqrt[2]}, a == -2 && b == I*Sqrt[2]}, {{a -> 2, b -> -Sqrt[2]}, a == 2 && b == -Sqrt[2]}, {{a -> 2, b -> Sqrt[2]}, a == 2 && b == Sqrt[2]}}
	];
Get[test]

label = "quadratic with u[x]"
variables = Association[
	"generators" -> {u[x]}, 
	"pars" -> {a, b},
	"expression" -> u[x]^2 - b u[x]^a + u[x]^b == 0,
	"result" -> {{{a->2,b->2},a==2&&b==2}}
		(*{{{b -> 2, a -> 2}, b == 2 && a == 2}}*)
	];
Get[test]

label = "independent and dependent variables"
variables = Association[
	"generators" -> {u[x],x}, 
	"pars" -> {a, b},
	"expression" -> u[x]^2 - b u[x]^a + u[x]^b + (b^2 - 4) x == 0,
	"result" -> {{{a->2,b->2},a==2&&b==2}}
		(*{{{b -> 2, a -> 2}, b == 2 && a == 2}}*)
	];
Get[test]

label = "avoid the singularity"
variables = Association[
	"generators" -> {u[x],v[x]}, 
	"pars" -> {a},
	"expression" -> a u[x]/v[x] == 0,
	"result" -> {{{a -> 0}, a == 0}}
	];
Get[test]

label = "empty"
variables = Association[
	"generators" -> {x}, 
	"pars" -> {a, b, c},
	"expression" -> {},
	"result" -> {{{}, True}}
	];
Get[test]
