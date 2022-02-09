from itertools import count
import copy
import time
global ne

def temp_var(temp, theta):
	for pred in temp:
		for i in range(len(pred.con_literal)):
			if(not pred.con_literal[i] in theta):
				continue
			pred.con_literal[i]=theta[pred.con_literal[i]]

def update_pred(lpred,pred):
	result=[]
	if(not isinstance(pred,Predicate_Sen)):
		return(result)
	temp=copy.deepcopy(lpred)
	for i in temp:
		if(i!=pred):
			result.append(i)
	return(result)


class kb_sentences:
	def __init__(self,knowledge_base_sentences,queries):
		self.sentences=knowledge_base_sentences
		self.queries=queries
		self.add_to_kb=[]
		self.list_sentence=[]
		self.sentence_find={}
		self.list_queries=[]
		for q in self.queries:
			self.list_queries.append(Solve_Sentences(q))
		for s in self.sentences:
			flag=Solve_Sentences(s)
			self.list_sentence.append(flag)
			for i in flag.predicate_list:
				if(i.predicate_temp in self.sentence_find and flag not in self.sentence_find[i.predicate_temp]):
					self.sentence_find[i.predicate_temp].append(flag)
				elif(i.predicate_temp not in self.sentence_find):
					self.sentence_find[i.predicate_temp]=[flag]
		self.result=self.ask_kb()

	def ask_kb(self):
		result=[]
		for q in self.list_queries:
			q.predicate_list[0].negation=not(q.predicate_list[0].negation)
			self.add_to_kb=[]
			self.add_to_kb.append(q)
			try:
				ans=self.resolve_sentence(q,1,[])
			except:
				ans=False
			result.append(ans)
		return(result)

	def is_sol(self,length,path):
		n=length
		if(n>0):
			for i in range(n-1):
				if(path[n-1]==path[i] or path[n-1]==self.add_to_kb[0]):
					return(False)
		return(True)

	def unify_literals(self,pred,pred1,theta):
		if(pred in theta):
			return(self.unify(theta[pred],pred1,theta))
		elif(pred1 in theta):
			return(self.unify(pred,theta[pred1],theta))
		else:
			if(not (isinstance(pred1,str) and pred1[0].isalpha() and pred1[0].islower())):
				theta[pred]=pred1
			return(theta)

	def unify(self,pred,pred1,theta):
		if("fail" not in theta):
			pass
		if("fail" in theta):
			return(theta)
		if(pred==pred1):
			return(theta)
		elif(isinstance(pred,str) and pred[0].isalpha() and pred[0].islower()):
			return(self.unify_literals(pred,pred1,theta))
		elif(isinstance(pred1,str) and pred1[0].isalpha() and pred1[0].islower()):
			return(self.unify_literals(pred1,pred,theta))
		elif(isinstance(pred,Predicate_Sen) and isinstance(pred1,Predicate_Sen)):
			return(self.unify(pred.con_literal,pred1.con_literal,self.unify(pred.predicate,pred1.predicate,theta)))
		elif(isinstance(pred,list) and isinstance(pred1,list)):
			return(self.unify(pred[1:],pred1[1:],self.unify(pred[0],pred1[0],theta)))
		else:
			theta['fail']=1
			return(theta)

	def not_unified(self):
		for i in self.list_sentence:
			if(not i.islower()):
				return(False)
		return(True)

	def resolve_pred(self,pred2,pred1):
		result_resolve=[]
		for i in pred2.predicate_list:
			for j in pred1.predicate_list:
				if((i.predicate==j.predicate) and not (i.negation==j.negation)):
					theta={}
					self.unify(i,j,theta)
					if('fail' not in theta):
						temp=update_pred(pred2.predicate_list[:],i)
						temp_var(temp,theta)
						temp1=update_pred(pred1.predicate_list[:],j)
						temp_var(temp1,theta)
						flag=Solve_Sentences()
						for pred in temp:
							if(pred and not (pred in flag)):
								flag.predicate_list.append(pred)
						for pred in temp1:
							if(pred and not (pred in flag)):
								flag.predicate_list.append(pred)
						result_resolve.append(flag)
		return(result_resolve)

	def remove(self):
		sen_list=[]
		for i in self.list_sentence:
			flag=False
			for j in self.list_sentence:
				if(j==i):
					flag=True
			if(flag==True):
				sen_list.append(i)
		return(sen_list)

	def resolve_sentence(self,query,number_query,path):
		x=[]
		flag=False
		if(not query or not query.predicate_list):
			return(True)
		if(number_query>0):
			n=len(path[:number_query-1])
			if(self.is_sol(n,path)):
				pass
			if(not self.is_sol(n,path)):
				return(False)
		for pred in query.predicate_list:
			if(not pred.negation):
				literal='~'+pred.predicate
			else:
				literal=pred.predicate
			if(literal not in self.sentence_find):
				pass
			else:
				x+=self.sentence_find[literal]
		x+=self.add_to_kb[:number_query]
		for pred in x:
			unified_sentence=self.resolve_pred(query,pred)
			if(not unified_sentence):
				continue
			self.add_to_kb.append(unified_sentence[0])
			path.append(unified_sentence[0])
			flag=self.resolve_sentence(unified_sentence[0],number_query+1,path)
			if(flag):
				return(True)
		return(flag)


class Predicate_Sen:
	def __init__(self,clause,implication):
		self.negation=False
		self.implication=implication
		self.negation=False
		self.predicate_temp=clause.strip().split('(')[0].strip()

		if(self.predicate_temp.strip()[0]=='~'):
			self.negation=True
			self.predicate=self.predicate_temp.strip()[1:]
		else:
			self.predicate=self.predicate_temp.strip()
		self.con_literal=clause.split('(')[1].replace(')', '').strip().split(',')
		for i,j in enumerate(self.con_literal):
			self.con_literal[i]=j.strip()
		
	def pred_update(self):
		self.new_pred='~'[not self.negation:]+self.predicate_temp

	def __ne__(self,var):
		if self.predicate_temp!=var.predicate_temp:
			return(True)
		if self.con_literal!=var.con_literal:
			return(True)
		return(False)

	def __eq__(self,var):
		return not self.__ne__(var)

	def not_unified(self):
		for i in self.predicate_temp:
			if(not i.islower()):
				return(False)
		return(True)

ne=count()
class Solve_Sentences:
	def __init__(self,sentence=None):
		self.solved_imp=[]
		self.premise_list=[]
		self.sen_list=sentence
		self.neg=False
		self.predicate_list=[]
		self.visited={}
		self.implication=False
		if(not sentence):
			return
		co=0
		if('=>' in sentence):
			self.implication=True
			var=sentence.split("=>")
			for i, j in enumerate(var):
				if(i==0 and '&' in j):
					var1=j.split('&')
					for k in var1:
						self.premise_list.append(Predicate_Sen(k,self.implication))
						co+=1
				elif(i==0):
					self.premise_list.append(Predicate_Sen(j,self.implication))
					co+=1
				else:
					self.solved_imp.append(Predicate_Sen(j,self.implication))
					co+=1

				self.predicate_list=self.premise_list+self.solved_imp
		else:
			self.predicate_list.append(Predicate_Sen(sentence,self.implication))

		if(self.implication):
			for i in self.premise_list:
				i.negation=not i.negation

		for predicate in self.predicate_list:
			for i, j in enumerate(predicate.con_literal):
				if(j.isalpha() and j.islower() and len(j)==1):
					if(j not in self.visited):
						new_j='x'+str(next(ne))
						self.visited[predicate.con_literal[i]]=new_j
						predicate.con_literal[i]=new_j
					else:
						predicate.con_literal[i] = self.visited[j]


	def remove(self):
		p_list=[]
		for i in self.premise_list:
			flag=False
			for j in self.predicate_list:
				if(j==i):
					flag=True
			if(flag==True):
				p_list.append(i)
		return(p_list)

	def __contains__(self,sen):
		for i in self.predicate_list:
			if(i!=sen):
				continue
			else:
				return(True)
		return(False)

	def remove_solved(self):
		s_list=[]
		for i in self.solved_imp:
			flag=False
			for j in self.sen_list:
				if(j==i):
					flag=True
			if(flag==True):
				s_list.append(i)
		return(s_list)

	def duplicate_remove(self):
		for i in self.predicate_list:
			i.remove()

	def __eq__(self,var):
		co=0
		for i in self.predicate_list:
			for j in var.predicate_list:
				if(i==j):
					co+= 1
		return(co==len(self.predicate_list)==len(var.predicate_list))

	def __ne__(self,var):
		return(not self.__eq__(var))


if __name__ == '__main__':
	file1=open('input.txt','r')
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
	f_result=kb_sentences(knowledge_base,queries)
	file2=open('output.txt','w+')
	for value,predicate in enumerate(f_result.result):
		if(value==0):
			file2.write(str(predicate).upper())
		else:
			file2.write('\n')
			file2.write(str(predicate).upper())
	file2.close()