**Output of command `agda --profile=internal Final-thms.agda`:**

```
Total                            9,940,526ms              
Miscellaneous                        1,872ms              
Typing                             701,103ms (8,639,700ms)
Typing.CheckRHS                  4,360,701ms              
Typing.OccursCheck               1,612,078ms              
Typing.InstanceSearch            1,331,200ms              
Typing.TypeSig                     627,715ms              
Typing.CheckLHS                      5,787ms     (6,878ms)
Typing.CheckLHS.UnifyIndices         1,091ms              
Typing.With                             22ms              
Serialization                      329,304ms   (412,528ms)
Serialization.BuildInterface        80,288ms              
Serialization.Compress               1,408ms              
Serialization.BinaryEncode           1,297ms              
Serialization.Sort                     228ms              
DeadCode                               184ms   (346,187ms)
DeadCode.DeadCodeInstantiateFull   329,535ms              
DeadCode.DeadCodeReachable          16,467ms              
Positivity                         310,860ms              
ProjectionLikeness                  73,659ms              
Termination                            171ms    (59,526ms)
Termination.RecCheck                59,332ms              
Termination.Compare                     16ms              
Coverage                            44,430ms    (45,342ms)
Coverage.UnifyIndices                  912ms              
Parsing                              1,090ms    (28,297ms)
Parsing.OperatorsExpr               26,042ms              
Parsing.OperatorsPattern             1,164ms              
Scoping                              1,386ms    (15,742ms)
Scoping.InverseScopeLookup          14,356ms              
Deserialization                      3,953ms     (5,469ms)
Deserialization.Compaction           1,516ms              
Highlighting                         1,016ms              
Import                                 260ms              
Injectivity                             66ms
```
