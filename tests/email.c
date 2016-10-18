#define MAX(X,Y)    ( ((X)>(Y))?(X):(Y) )

int main(int argc, char **argv){
    int j ,k;
    for( j = 0; j < argc; j++ ){
        for( k = 0; k < argc; k++ ) {
	    if( MAX(j,k) ||  j ) continue;
	}
    }
}
