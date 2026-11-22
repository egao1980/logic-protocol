# logic-protocol

CLOS logic protocol for cl-stack (nickname `stack-logic`), slice L0 of Track L:

- terms, atoms and facts as plain data (`(edge 1 2)`, logic variables `?x`), one defined order (`term<`, `fact<`) for every list returned;
- rules `(rule HEAD :- BODY…)` with negation, built-ins (`=`, `/=`, `<`…, `glob`, `prefix`), Dedalus time-step heads `(next …)`, and the ASP shapes (`(rule :- …)`, `(choice LO HI …)`) parsed for later backends;
- range-restriction and stratification checks (`rule-unsafe-variables`, `stratify`);
- programs: `make-program`, `add-rule(s)`, `assert-fact`, `retract-fact`, an incremental `update` returning a `delta` (added / removed facts of the model), `query` / `holds-p` with `:assume`, `explain` (proof tree or why-not trace), `tick`;
- budgets on every operation, and CLHS 9 conditions with restarts: `logic-unsafe-rule`, `logic-unstratifiable` (`drop-rule`, `use-backend`), `logic-unsupported-rule`, `logic-budget-exceeded` (`continue`, `use-value`), `logic-no-backend`.

No backend inside. The default is [logic-backend-datalog](https://github.com/egao1980/logic-backend-datalog).

## Systems

| System | What |
|--------|------|
| `logic-protocol` | the protocol |
| `logic-protocol/tests` | protocol tests on a mock backend (checks, restarts, migration, normalization, budgets) |
| `logic-protocol/conformance` | the backend conformance suite: runs against `*logic-backend*`, skips what a backend's `backend-features` lack. Every backend (Datalog now, ASP in L5, Prolog in L6) runs it from its own test-op |

Design: [cl-stack/docs/capabilities/logic.md](https://github.com/egao1980/cl-stack/blob/main/docs/capabilities/logic.md).

## License

MIT — see [LICENSE](LICENSE).
