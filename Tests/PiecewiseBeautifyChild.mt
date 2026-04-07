(* Wolfram Language Test file *)

Test[
    With[{expression = variables["expression"], result = variables["result"]},
        With[{computation = PiecewiseBeautify[expression]},
            Which[
                Expand[result] === Expand[computation],
                True,
                PiecewiseEqualOperator[variables][result, computation] === True,
                True,
                True,
                {computation, variables}
            ]
        ]
    ]
    ,
    True
    ,
    TestID -> "PiecewiseBeautify-20210121-K6RH82_" <> label
]
