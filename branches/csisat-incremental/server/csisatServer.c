/*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *
 *  Copyright (C) 2007-2008  Dirk Beyer and Damien Zufferey.
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CSIsat web page:
 *    http://www.cs.sfu.ca/~dbeyer/CSIsat/
 */

#include <sys/types.h> 
#include <stdio.h>    
#include <unistd.h>   
#include <stdlib.h>   
#include <sys/stat.h> 
#include <sys/wait.h> 
#include <errno.h>
#include <signal.h>
#include <fcntl.h>
#include <string.h>
#include <pthread.h>


#define NBSOLVER 1
//TODO why it only works with one thread ??
//what library call should be protected

typedef struct {
	pthread_t thread;
	pid_t child;
	int pipe_to_solver[2];
	int pipe_from_solver[2];
} solver;

void init_solver(solver* s){
	s->child = 0;
	if(pipe(s->pipe_to_solver) != 0){
		perror("creating the pipe for child-parent communication (to child)");
		exit(-1);
	}
	if(pipe(s->pipe_from_solver) != 0){
		perror("creating the pipe for child-parent communication (from child)");
		exit(-1);
	}
}

solver solvers[NBSOLVER];

//the arguments passed to this process
char* const * args = NULL;

pthread_mutex_t mutex;

int init_mutex(){
	int e = pthread_mutex_init( &mutex, NULL);
	if( e != 0 ){
		perror("error: creating the pthread_mutex_t. ");
	}
	return e;
}

void destroy_mutex(){
	pthread_mutex_destroy(&mutex);
}

int counter = 0;//count the number of process created

/*do not takes care of error, just clean*/
void terminate(){
	//kill the child processes
	int i;
	for( i = 0; i < NBSOLVER; ++i){
		int child = solvers[i].child;
		if( child > 0 ){
			kill(child, SIGKILL);
		}
	}
	//destroy_mutex();
	printf("csisatServer stopped (%d queries)\n", counter-NBSOLVER);
}

void create(solver* s){
	++counter;
	init_solver(s);
	//fork + multithreading => danger
	//but the only existing thread in the child should be this one.
	s->child = fork();
	if ( s->child == 0 ){
		//child part
		dup2(s->pipe_to_solver[0], STDIN_FILENO);//redirect in
		dup2(s->pipe_from_solver[1], STDERR_FILENO);//redirect err
		dup2(s->pipe_from_solver[1], STDOUT_FILENO);//redirect stdout
		if(close(s->pipe_from_solver[0]) != 0){ perror("closing pipe"); }
		if(close(s->pipe_from_solver[1]) != 0){ perror("closing pipe"); }
		if(close(s->pipe_to_solver[0]) != 0){ perror("closing pipe"); }
		if(close(s->pipe_to_solver[1]) != 0){ perror("closing pipe"); }
		execvp("csisat", args);
		perror("error during execvp ");
		terminate();
		exit(666);
	}else if (s->child == -1){
		//error part
		printf("error creating the %dth process\n", counter);
		terminate();
		exit(0);
	}else{
		//parent part
		//printf("child: %d\n", s->child);fflush(stdout);//DEBUG
		if(close(s->pipe_to_solver[0]) != 0){//close anyway, only used by the child
			perror("line: __LINE__");
		}
		if(close(s->pipe_from_solver[1]) != 0){//close anyway, only used by the child
			perror("line: __LINE__");
		}
	}
}

int forward_answer(FILE* in, FILE* out){
	char c = (char) fgetc(in);
	while(c != EOF){
		if(putc(c, out) == EOF){
			perror("forwarding answer from CsiSat");
		}
		c = (char) fgetc(in);
	}
	return 0;
}

int forward_query(FILE* in, FILE* out){
	int counter = 0;
	char c = (char) fgetc(in);
	while(c != EOF && c != '\n'){
        ++counter;
		if(putc(c, out) == EOF){
			perror("forwarding query to CsiSat");
		}
		c = (char) fgetc(in);
	}
	//put a line return
	putc('\n', out);
	return counter;
}


//int white_line_counter = 0;

void* read_from_stdin(void* v){
	solver* s = (solver*) v;
	while(! feof(stdin)){ //&& white_line_counter < 10){
		create(s);
		FILE* out = fdopen( s->pipe_to_solver[1], "w");
		if( out == NULL){
			perror("opening pipe to CsiSat");
		}
		
		FILE* in = fdopen( s->pipe_from_solver[0], "r");
		if( in == NULL){
			perror("opening pipe from CsiSat");
		}
		
		if(pthread_mutex_lock(&mutex) != 0){
			perror("locking mutex ");
		}
		
		if(forward_query(stdin, out) <= 0){
            continue;//TODO UGLY
			//++white_line_counter;//not to do like clp and loop forever when blast crash
		}
		
		if(fclose(out) != 0){
			perror("closing pipe to solver");
		}
		
		forward_answer(in, stdout);
		fflush(stdout);
		//TODO syncro fin
		if(pthread_mutex_unlock(&mutex) != 0){
			perror("unlocking mutex ");
		}
		
		if(fclose(in) != 0){
			perror("closing pipe from solver");
		}
		
		if(waitpid(s->child, NULL, 0) == -1){
			perror("waitpid failed");
		}
		
		s->child = 0;
	}
	return NULL;
}

void signal_handler(int sig){
	terminate();
	fprintf(stderr, "RECEIVED SIGNAL %d, exiting\n", sig);
	exit(0);
}

void sig_pipe(int sig){
	//fprintf(stderr, "RECEIVED SIGNAL %d, SIGPIPE\n", sig);
}

void setup_signal_hanlder(){
	signal(SIGQUIT, signal_handler);
	signal(SIGABRT, signal_handler);
	signal(SIGALRM, signal_handler);
	signal(SIGHUP, signal_handler);
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);
	signal(SIGSEGV, signal_handler);
	signal(SIGPIPE, sig_pipe);
}

int main(int argc, char* argv[]){
    args = argv;
	setup_signal_hanlder();
	init_mutex();
	int i;
	for(i = 1; i < NBSOLVER; ++i){
		if(pthread_create(&(solvers[i].thread), NULL, &read_from_stdin, &(solvers[i])) != 0){
			fprintf( stderr, "failed to create thread. \n");
			terminate();
			exit(-1);
		}
	}
	read_from_stdin(&(solvers[0]));
	terminate();
	return 0;
}
