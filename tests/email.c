
int main(int argc, char **argv){
    int j ,k;
     for( j = 0; j < argc; j++ ){
//         sigma( j )_True  ;  sigma1( argc )_True
         for( k = 0; k < argc; k++ ) { // check k < sigma1
  //       	   sigma2( k )_True, 
 	            if( j>k ? j : k) { 
 //	                 check sigma > sigma2 (if interno)
 //	                 sigma4(sigma -> j)_True and compares to 0 (if externo)
//	       	sigma6(sigma2 -> k)_False and compares to 0 (if externo)
	       	   	       	
	       	continue;
	             }
	        } //sigma3(sigma1->argc)_False
     }    
}


