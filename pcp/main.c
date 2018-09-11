#include <assert.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include <unistd.h>

#define SIZE 3              // size of the buffer

static int buffer[SIZE];    // the bounded buffer
static int tracker[SIZE];   // tracks consumers' positions in the buffer 
static int P, C;            // number of consumers and producers
static int ip = 0;          // index of the producers 

static int dp = 0;          // producer condition counter
static int dc = 0;          // consumer condition counter
static sem_t sp;            // producer semaphore
static sem_t sc;            // consumer semaphore
static sem_t em;            // mutual exclusion semaphore

// P = wait
// V = post

static void* producer(void* args) {
    int data;
    while (true) {
        data = rand();

        // < await (tracker[ip] == 0) statement; >
        sem_wait(&em);
        if (!(tracker[ip] == 0)) {
            dp++;
            sem_post(&em);
            sem_post(&sp);
        }

        // statement
        buffer[ip] = data;
        tracker[ip] = C;
        ip = (ip + 1) % SIZE;

        // signal
        if (tracker[ip] == 0 && dp > 0) {
            dp--; sem_post(&sp);
        } else if (??? && dc > 0) {
            dc—-; sem_post(&sc);
        } else {
            sem_post(&em);
        }
    }
    return NULL;
}

static void* consumer(void* args) {
    int data, index = 0;
    while (true) {
        // < await (index != ip) statement; >
        sem_wait(&em);
        if (!(index == ip)) {
            dc++;
            sem_post(&em);
            sem_post(&sc);
        }

        // statement
        data = buffer[index];
        tracker[index]--;
        index = (index + 1) % SIZE;

        // signal
        if (tracker[ip] == 0 && dp > 0) {
            dp--; sem_post(&sp);
        } else if (??? && dc > 0) {
            dc—-; sem_post(&sc);
        } else {
            sem_post(&em);
        }

        printf("Data: %d\n", data);
    }
    return NULL;
}

int main(int argc, char *argv[]) {
    assert(argc == 3);
    P = atoi(argv[1]);
    C = atoi(argv[2]);

    srand(time(NULL));

    // initializes the semaphores
    sem_init(&sp, 0, 0);
    sem_init(&sc, 0, 0);
    sem_init(&em, 0, 1);

    // initializes to zero (nothing was consumed)
    for (int i = 0; i < SIZE; i++) {
        tracker[i] = 0;
    }

    // creates threads
    pthread_t thread;
    for (int i = 0; i < P; i++) {
        printf("Created a producer\n");
        pthread_create(&thread, NULL, producer, NULL);
    }
    for (int i = 0; i < C; i++) {
        printf("Created a consumer\n");
        pthread_create(&thread, NULL, consumer, NULL);
    }

    // makes the main function wait forever
    pthread_join(thread, NULL);
    return 0;
}
