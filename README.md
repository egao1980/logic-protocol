# logic-protocol

CLOS logic protocol for cl-stack (nickname `stack-logic`): facts and relations, rules, queries, assert / retract, an incremental `update` that returns the delta of derived facts, proofs and why-not traces, budgets, conditions with restarts. No backend inside; the default backend is [logic-backend-datalog](https://github.com/egao1980/logic-backend-datalog). Slice L0 of Track L.

Design: [cl-stack/docs/capabilities/logic.md](https://github.com/egao1980/cl-stack/blob/main/docs/capabilities/logic.md). Scaffold only; the first version lands through team-solve.

## License

MIT — see [LICENSE](LICENSE).
