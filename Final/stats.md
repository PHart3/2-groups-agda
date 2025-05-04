**Output of command `agda --profile=internal Final-thms.agda`:**

```
Total                            9,923,000ms              
Miscellaneous                        1,227ms              
Typing                             711,505ms (8,687,286ms)
Typing.CheckRHS                  4,439,228ms              
Typing.OccursCheck               1,613,622ms              
Typing.InstanceSearch            1,274,519ms              
Typing.TypeSig                     643,616ms              
Typing.CheckLHS                      3,914ms     (4,785ms)
Typing.CheckLHS.UnifyIndices           871ms              
Serialization                      308,909ms   (386,271ms)
Serialization.BuildInterface        75,433ms              
Serialization.Compress                 987ms              
Serialization.BinaryEncode             781ms              
Serialization.Sort                     159ms              
DeadCode                               141ms   (352,553ms)
DeadCode.DeadCodeInstantiateFull   317,407ms              
DeadCode.DeadCodeReachable          35,004ms              
Positivity                         295,325ms              
ProjectionLikeness                  62,339ms              
Termination                            116ms    (53,302ms)
Termination.RecCheck                53,169ms              
Termination.Compare                     13ms              
Coverage                            47,800ms    (48,510ms)
Coverage.UnifyIndices                  709ms              
Parsing                                802ms    (18,791ms)
Parsing.OperatorsExpr               17,308ms              
Parsing.OperatorsPattern               680ms              
Scoping                              1,011ms    (12,194ms)
Scoping.InverseScopeLookup          11,183ms              
Deserialization                      3,107ms     (4,160ms)
Deserialization.Compaction           1,053ms              
Highlighting                           718ms              
Import                                 286ms              
Injectivity                             43ms
```
