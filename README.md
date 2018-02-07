
### Format for input.txt:      
\<NQ = NUMBER OF QUERIES\>  
\<QUERY 1\>    
…    
\<QUERY NQ\>  
\<NS = NUMBER OF GIVEN SENTENCES IN THE KNOWLEDGE BASE\>   
\<SENTENCE 1\>   
…     
\<SENTENCE NS\>       
where   
• Each query will be a single literal of the form Predicate(Constant) or ~Predicate(Constant).    
• Variables are all single lowercase letters.     
• All predicates (such as Sibling) and constants (such as John) are case-sensitive alphabetical strings that    
begin with an uppercase letter.    
• Each predicate takes at least one argument. Predicates will take at most 100 arguments. A given    
predicate name will not appear with different number of arguments.    
• There will be at most 100 queries and 1000 sentences in the knowledge base. 
• You can assume that the input format is exactly as it is described. There will be no syntax errors in the     
given input.    

### Format for output.txt:        
For each query, determine if that query can be inferred from the knowledge base or not, one query per line:    
\<ANSWER 1\>   
…     
\<ANSWER NQ\>    
where   
each answer should be either TRUE if you can prove that the corresponding query sentence is true given the    
knowledge base, or FALSE if you cannot.    
