#include <assert.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include <unistd.h>

#define seminit(s, n, v) {sem_unlink(n); s = sem_open(n, O_CREAT, 0644, v);}
#define semup(s)         sem_post(s)
#define semdown(s)       sem_wait(s)

#define MALLOC(x, t)          x = (t*)malloc(sizeof(t));     if (!x) exit(1);
#define MALLOC_ARRAY(x, t, n) x = (t*)malloc(n * sizeof(t)); if (!x) exit(1);

#define SIZE 10             // size of the buffer

static int buffer[SIZE];    // the bounded buffer
static int tracker[SIZE];   // tracks consumers' positions in the buffer
static int P, C;            // number of consumers and producers
static int ip = 0;          // index of the producers
static int* ics;            // indexes of the consumers

static int dp = 0;          // producer condition counter
static int dc = 0;          // consumer condition counter
static sem_t* sp;           // producer mutex
static sem_t** scs;         // consumers' mutex
static sem_t* cr;           // critical region mutex

static void* producer(void* id_pointer) {
    int id = *((int*)id_pointer);
    free(id_pointer);

    int data;

    while (true) {
        data = rand() % 100;

        // < await (tracker[ip] == 0) statement; >
        semdown(cr);
        if (tracker[ip] != 0) {
            dp++; semup(cr); semdown(sp);
        }

        // statement
        buffer[ip] = data;
        printf("ID %d produced %d for index %d\n", id, data, ip);
        tracker[ip] = C;
        ip = (ip + 1) % SIZE;
        printf("new ip = %d\n", ip);

        // signal
        if (tracker[ip] == 0 && dp > 0) {
            dp--; semup(sp);
        } else {
            for (int i = 0; i < C; i++) {
                if (ics[i] != ip && dc > 0) {
                    dc--;
                    semup(scs[i]);
                    goto END;
                }
            }
            semup(cr);
            END:;
        }

        sleep(1);
    }
    return NULL;
}

static void* consumer(void* id_pointer) {
    int id = *((int*)id_pointer);
    free(id_pointer);

    int data;

    while (true) {
        // < await (ics[id] != ip) statement; >
        semdown(cr);
        if (ics[id] == ip) {
            dc++; semup(cr); semdown(scs[id]);
        }

        // statement
        data = buffer[ics[id]];
        printf("ID %d consumed %d from index %d\n", id, data, ics[id]);
        tracker[ics[id]]--;
        printf("[");
        for (int i = 0; i < SIZE; i++) {
            printf("%d, ", tracker[i]);
        }
        printf("]\n");
        ics[id] = (ics[id] + 1) % SIZE;
        printf("new index = %d\n", ics[id]);

        // signal
        if (tracker[ip] == 0 && dp > 0) {
            dp--; semup(sp);
        } else {
            for (int i = 0; i < C; i++) {
                if (ics[i] != ip && dc > 0) {
                    dc--;
                    semup(scs[i]);
                    goto END;
                }
            }
            semup(cr);
            END:;
        }

        sleep(1);
    }
    return NULL;
}

int main(int argc, char *argv[]) {
    assert(argc == 3);
    P = atoi(argv[1]);
    C = atoi(argv[2]);

    srand(time(NULL));

    // initializes the semaphores
    seminit(sp, "/sem-prod", 0);
    MALLOC_ARRAY(scs, sem_t*, C);
    for (int i = 0; i < C; i++) {
        char name[20];
        sprintf(name, "/sem-con-%d", i);
        seminit(scs[i], name, 0);
    }
    seminit(cr, "/sem-cr", 1);

    // consumers' indexes
    MALLOC_ARRAY(ics, int, C);
    for (int i = 0; i < C; i++) {
        ics[i] = 0;
    }

    // initializes to zero (nothing was consumed)
    for (int i = 0; i < SIZE; i++) {
        tracker[i] = 0;
    }

    // creates threads
    pthread_t thread;
    for (int i = 0; i < P; i++) {
        int* id; MALLOC(id, int); *id = i * 10;
        pthread_create(&thread, NULL, producer, (void*)id);
    }
    for (int i = 0; i < C; i++) {
        int* id; MALLOC(id, int); *id = i;
        pthread_create(&thread, NULL, consumer, (void*)id);
    }

    // makes the main function wait forever
    pthread_join(thread, NULL);
    return 0;
}
