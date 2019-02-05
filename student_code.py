import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        print("SUPPORTS:" , fact_or_rule.supports_facts, fact_or_rule.supports_rules)
        ####################################################
        # Student code goes here
        # have to check if the fact is in the kb

        if isinstance(fact_or_rule, Fact):
            try:
                find = self.facts.index(fact_or_rule)
                fact_or_rule = self.facts[find]
            except ValueError:
                print("fact not currently in kb")
            if not fact_or_rule.supported_by:

                if fact_or_rule.supports_facts:
                    for f in fact_or_rule.supports_facts:
                        try:
                            find = f.supported_by.index(fact_or_rule)
                            del f.supported_by[find]
                            del f.supported_by[find]
                        except ValueError:
                            pass
                        if (not f.asserted) and len(f.supported_by) == 0:
                            self.kb_retract(f)

                if fact_or_rule.supports_rules:
                    for r in fact_or_rule.supports_rules:
                        try:
                            find = r.supported_by.index(fact_or_rule)
                            del r.supported_by[find]
                            del r.supported_by[find]
                        except ValueError:
                            pass
                        if (not r.asserted) and len(r.supported_by) == 0:
                            self.kb_retract(r)

                self.facts.remove(fact_or_rule)

        elif isinstance(fact_or_rule, Rule):
            try:
                find = self.rules.index(fact_or_rule)
                fact_or_rule = self.rules[find]
            except ValueError:
                print("rule not in kb")
            if not fact_or_rule.asserted and not fact_or_rule.supported_by:

                if fact_or_rule.supports_facts:
                    for f in fact_or_rule.supports_facts:
                        try:
                            find = f.supported_by.index(fact_or_rule)
                            del f.supported_by[find]
                            del f.supported_by[find - 1]
                        except ValueError:
                            pass
                        if (not f.asserted) and len(f.supported_by) == 0:
                            self.kb_retract(f)

                if fact_or_rule.supports_rules:
                    for r in fact_or_rule.supports_rules:
                        try:
                            find = r.supported_by.index(fact_or_rule)
                            del f.supported_by[find]
                            del f.supported_by[find - 1]
                        except ValueError:
                            pass
                        if (not r.asserted) and len(r.supported_by) == 0:
                            self.kb_retract(r)

                self.rules.remove(fact_or_rule)

        

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        lob = match(fact.statement, rule.lhs[0])
        if lob:
            if len(rule.lhs) == 1:
                newstatement = instantiate(rule.rhs, lob)
                newfact = Fact(newstatement)
                newfact.supported_by += [fact, rule]
                newfact.asserted = False
                fact.supports_facts.append(newfact)
                rule.supports_facts.append(newfact)
                kb.kb_assert(newfact)
            else:
                newlhs = []
                for statement in rule.lhs[1:]:
                    newlhs += [instantiate(statement, lob)]
                newrule = Rule([newlhs, instantiate(rule.rhs, lob)])
                newrule.supported_by += [fact, rule]
                newrule.asserted = False
                fact.supports_rules.append(newrule)
                rule.supports_rules.append(newrule)
                kb.kb_assert(newrule)


