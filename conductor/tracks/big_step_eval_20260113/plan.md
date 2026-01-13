# Track Plan: Refactor IR Evaluator to a Big-Step Interpreter

## Phase 1: Foundation and Simple Expressions [checkpoint: 8a5e983]
- [x] Task: Define Value and Environment types for Big-Step Evaluation 59a95a5
- [x] Task: Implement Big-Step Evaluation for Literals and Variables 31032d2
- [x] Task: Implement Big-Step Evaluation for Basic Binary Operations 3ae5cc1
- [x] Task: Conductor - User Manual Verification 'Phase 1: Foundation' (Protocol in workflow.md) 8a5e983

## Phase 2: Functions and Control Flow [checkpoint: 815a440]
- [x] Task: Implement Big-Step Evaluation for Lambda and Application d43f3ac
- [x] Task: Implement Big-Step Evaluation for Label and Goto 0d66dd7
- [x] Task: Implement Big-Step Evaluation for Built-in functions 3bf18de
- [x] Task: Conductor - User Manual Verification 'Phase 2: Functions and Control' (Protocol in workflow.md) 815a440

## Phase 3: Data and Codata
- [x] Task: Implement Big-Step Evaluation for Records and Field Access c191886
- [ ] Task: Implement Big-Step Evaluation for Data Constructors and Pattern Matching
- [ ] Task: Implement Big-Step Evaluation for Codata and Copattern Matching
- [ ] Task: Conductor - User Manual Verification 'Phase 3: Data and Codata' (Protocol in workflow.md)

## Phase 4: Integration and Finalization
- [ ] Task: Integrate Big-Step Evaluator into Main CLI and REPL
- [ ] Task: Create consistency tests comparing Small-Step and Big-Step evaluation results
- [ ] Task: Run all existing golden tests using the Big-Step Evaluator
- [ ] Task: Conductor - User Manual Verification 'Phase 4: Integration' (Protocol in workflow.md)
