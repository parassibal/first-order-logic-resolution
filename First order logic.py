import time
from itertools import count
import copy

global var_tracker
var_tracker = count()


class Solve_Sentences:
    def __init__(self, sentence=None):
        self.input_s = sentence
        self.list_predicate = []
        self.premises_obj = []
        self.conclusion_obj = []
        self.implication = False
        self.seen_variables = {}
        if not sentence:
            return

        # Add premises and conclusions for implication
        if '=>' in sentence:
            self.implication = True
            temp_list = sentence.split("=>")
            for i, idx in enumerate(temp_list):
                if i == 0 and '&' in idx:
                    temp_idx = idx.split('&')
                    for t_idx in temp_idx:
                        self.premises_obj.append(PredicateClass(t_idx, self.implication))
                elif i == 0:

                    self.premises_obj.append(PredicateClass(idx, self.implication))
                else:

                    self.conclusion_obj.append(PredicateClass(idx, self.implication))
                self.list_predicate = self.premises_obj + self.conclusion_obj

        else:
            self.list_predicate.append(PredicateClass(sentence, self.implication))

        # Eliminate implication
        if self.implication:
            for premise in self.premises_obj:
                premise.negation = not premise.negation

        for predicate in self.list_predicate:
            for i, argument in enumerate(predicate.constant_arguments):
                if argument.isalpha() and argument.islower() and len(argument) == 1:
                    if argument not in self.seen_variables:
                        st_argument = 'x' + str(next(var_tracker))
                        self.seen_variables[predicate.constant_arguments[i]] = st_argument
                        predicate.constant_arguments[i] = st_argument
                    else:
                        predicate.constant_arguments[i] = self.seen_variables[argument]

    def __eq__(self, other):
        f = 0
        for i in self.list_predicate:
            for j in other.list_predicate:
                if i == j:
                    f += 1

        return f == len(self.list_predicate) == len(other.list_predicate)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __contains__(self, item):

        for pred in self.list_predicate:
            if pred != item:
                continue
            else:
                return True
        return False

    def dump_sentences(self):

        for pred in self.list_predicate:
            pred.dump_predicate()


class PredicateClass:
    def __init__(self, sentence, implication):
        self.t_predicate = sentence.strip().split('(')[0].strip()
        self.implication = implication
        self.negation = False
        if self.t_predicate.strip()[0] == '~':
            self.predicate = self.t_predicate.strip()[1:]
            self.negation = True
        else:
            self.predicate = self.t_predicate.strip()
        self.constant_arguments = sentence.split('(')[1].replace(')', '').strip().split(',')

        for i, arg in enumerate(self.constant_arguments):
            self.constant_arguments[i] = arg.strip()

    def __ne__(self, other):
        if self.t_predicate != other.t_predicate:
            return True
        if self.constant_arguments != other.constant_arguments:
            return True
        return False

    def __eq__(self, other):
        return not self.__ne__(other)


def update_predicate(predicate, predicate_list):
    l_1 = []
    if not isinstance(predicate, PredicateClass):
        return l_1

    new_pred = copy.deepcopy(predicate_list)
    for x in new_pred:
        if x != predicate:
            l_1.append(x)
    return l_1


def temp_var(all_predicates, var_map):
    for predicate in all_predicates:
        for i in range(len(predicate.constant_arguments)):
            if not predicate.constant_arguments[i] in var_map:
                continue
            predicate.constant_arguments[i] = var_map[predicate.constant_arguments[i]]


class KBClass:
    def __init__(self, sentences, queries):
        self.input_sentences = sentences
        self.queries = queries
        self.sentences_obj = []
        self.sentence_find = {}
        self.list_queries = []
        self.add_to_kb = []

        for query in self.queries:
            self.list_queries.append(Solve_Sentences(query))

        # Add to KB
        for sentence in self.input_sentences:
            flag = Solve_Sentences(sentence)
            self.sentences_obj.append(flag)

            for premise in flag.list_predicate:

                if premise.t_predicate in self.sentence_find and flag not in self.sentence_find[premise.t_predicate]:
                    self.sentence_find[premise.t_predicate].append(flag)
                elif premise.t_predicate not in self.sentence_find:
                    self.sentence_find[premise.t_predicate] = [flag]

        self.result = self.ask_kb()

    def variable_unify(self, var, x, theta):

        if var in theta:
            return self.unify(theta[var], x, theta)
        elif x in theta:
            return self.unify(var, theta[x], theta)
        else:
            if not (isinstance(x, str) and x[0].isalpha() and x[0].islower()):
                theta[var] = x
            return theta

    def unify(self, x, y, theta):

        if 'fail' in theta:
            return theta

        if x == y:
            return theta
        elif isinstance(x, str) and x[0].isalpha() and x[0].islower():
            return self.variable_unify(x, y, theta)
        elif isinstance(y, str) and y[0].isalpha() and y[0].islower():
            return self.variable_unify(y, x, theta)
        elif isinstance(x, PredicateClass) and isinstance(y, PredicateClass):
            return self.unify(x.constant_arguments, y.constant_arguments,
                                    self.unify(x.predicate, y.predicate, theta))
        elif isinstance(x, list) and isinstance(y, list):
            return self.unify(x[1:], y[1:], self.unify(x[0], y[0], theta))
        else:
            theta['fail'] = 1
            return theta

    def resolve_pred(self,pred1,pred2):
        result_resolve=[]
        for i in pred1.list_predicate:
            for j in pred2.list_predicate:
                if((i.predicate==j.predicate) and not (i.negation==j.negation)):
                    theta={}
                    self.unify(i,j,theta)
                    if('fail' not in theta):
                        temp=update_predicate(i,pred1.list_predicate[:])
                        temp_var(temp,theta)
                        temp1=update_predicate(j,pred2.list_predicate[:])
                        temp_var(temp1, theta)

                        flag=Solve_Sentences()
                        for pred in temp:
                            if(pred and not (pred in flag)):
                                flag.list_predicate.append(pred)
                        for pred in temp1:
                            if(pred and not (pred in flag)):
                                flag.list_predicate.append(pred)

                        temp_s.append(flag)
        return temp_s

    def is_sol(self,path,length):
        if(length>0):
            for i in range(length-1):
                if(path[length-1]==path[i] or path[length-1]==self.add_to_kb[0]):
                    return False
        return True

    def resolve_sentence(self,query,number_query,path):
        x=[]
        result=False
        if(not query or not query.list_predicate):
            return(True)
        if(number_query>0):
            length=len(path[:number_query-1])
            if(not self.is_sol(path,length)):
                return(False)
        for q in query.list_predicate:
            if(not q.negation):
                literal='~'+q.predicate
            else:
                literal=q.predicate
            if(literal not in self.sentence_find):
                pass
            elif(literal in self.sentence_find):
                x+=self.sentence_find[literal]
        x+=self.add_to_kb[:number_query]

        for i in x:
            unified_sentence=self.resolve_pred(query,i)
            if(not unified_sentence):
                continue
            self.add_to_kb.append(unified_sentence[0])
            path.append(unified_sentence[0])
            result=self.resolve_sentence(unified_sentence[0],number_query+1,path)
            if(result):
                return True
        return(result)



    def ask_kb(self):
        result=[]
        for q in self.list_queries:
            q.list_predicate[0].negation=not q.list_predicate[0].negation
            self.add_to_kb=[]
            self.add_to_kb.append(q)
            try:
                ans=self.resolve_sentence(q,1,[])
            except:
                ans=False
            result.append(ans)

        return(result)


if __name__ == '__main__':
	file1=open('/users/paras/Desktop/input.txt','r')
	no_of_queries=file1.readline().strip()
	no_of_queries=int(no_of_queries)
	queries=[]
	for i in range(no_of_queries):
		q_list=file1.readline().strip()
		queries.append(q_list)
	no_of_sentences=file1.readline().strip()
	no_of_sentences=int(no_of_sentences)
	knowledge_base=[]
	for i in range(no_of_sentences):
		sentences=file1.readline().strip()
		knowledge_base.append(sentences)
	file1.close
	f_result=KBClass(knowledge_base,queries)
	file2=open('/users/paras/Desktop/output.txt','w+')
	for value,predicate in enumerate(f_result.result):
		if(value==0):
			file2.write(str(predicate).upper())
		else:
			file2.write('\n')
			file2.write(str(predicate).upper())
	file2.close()