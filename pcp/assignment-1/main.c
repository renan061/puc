#include <assert.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include <unistd.h>

#define seminit(s, n, v) { sem_unlink(n); s = sem_open(n, O_CREAT, 0644, v);  }
#define semdown(s, i, n) { sem_wait(s); /* printf("ID %d got %s\n" , i, n); */}
#define semup(s, i, n)   { sem_post(s); /* printf("ID %d lost %s\n", i, n); */}

#define MALLOC(x, t)          x = (t*)malloc(sizeof(t));     if (!x) exit(1);
#define MALLOC_ARRAY(x, t, n) x = (t*)malloc(n * sizeof(t)); if (!x) exit(1);

#define SIZE 10              // size of the buffer

static int p, c;             // number of consumers and producers

static int tracker[SIZE];    // tracks data status with consumers
static int buffer[SIZE];     // the bounded buffer
static int nextfree = 0;     // next availabe position for the producer
static int* nextdata;        // current position for consumers (indexed by id)

static int dp = 0;           // producer condition counter
static int* dc;              // consumers condition counters (indexed by id)
static sem_t* sp;            // semaphore producer
static sem_t** sc;           // semaphore consumer (indexed by consumer id)
static sem_t* scr;           // semaphore critical region

// auxiliary functions
static pthread_t create_thread(int id, void*(function)(void*));
static void print_buffer_tracker(void);
static void signal_(int id);

static void* producer(void* id_pointer) {
    int id = *((int*)id_pointer);
    free(id_pointer);

    int data;

    while (true) {
        data = 10 + (rand() % 80);

        semdown(scr, id, "a-scr");
        if (!(tracker[nextfree] == 0)) {
            dp++;
            semup(scr, id, "a-scr");
            semdown(sp, id, "a-sp");
        }

        buffer[nextfree] = data;
        tracker[nextfree] = c;

        printf("ID %d produced %d for index %d", id, data, nextfree);
        print_buffer_tracker();

        nextfree = (nextfree + 1) % SIZE;

        signal_(id);

        // sleep(1);
    }
    return NULL;
}

static void* consumer(void* id_pointer) {
    int id = *((int*)id_pointer);
    free(id_pointer);

    int data;

    while (true) {
        semdown(scr, id, "a-scr");
        if (!(tracker[nextdata[id]] > 0)) {
            dc[id]++;
            semup(scr, id, "a-scr");
            semdown(sc[id], id, "a-sc");
        }

        data = buffer[nextdata[id]];
        tracker[nextdata[id]]--;

        printf("ID %d consumed %d from index %d", id, data, nextdata[id]);
        print_buffer_tracker();

        nextdata[id] = (nextdata[id] + 1) % SIZE;

        signal_(id);

        // sleep(1);
    }
    return NULL;
}

int main(int argc, char *argv[]) {
    assert(argc == 3);
    p = atoi(argv[1]);
    c = atoi(argv[2]);

    srand(time(NULL));

    // initializes the semaphores
    seminit(sp , "/sem-producer", 0);
    seminit(scr, "/sem-cr"      , 1);
    MALLOC_ARRAY(sc, sem_t*, c);
    for (int i = 0; i < c; i++) {
        char name[30];
        sprintf(name, "/sem-consumer-%d", i);
        seminit(sc[i], name, 0);
    }

    // initializes arrays nextdata, dc, tracker, and buffer
    MALLOC_ARRAY(nextdata, int, c);
    MALLOC_ARRAY(dc, int, c);
    for (int i = 0; i < c; i++)    { nextdata[i] = 0;  }
    for (int i = 0; i < c; i++)    { dc[i]       = 0;  }
    for (int i = 0; i < SIZE; i++) { tracker[i]  = 0;  }
    for (int i = 0; i < SIZE; i++) { buffer[i]   = 95; }

    // creates threads
    semdown(scr, -1, "scr");
    pthread_t thread;
    for (int i = 0; i < p; i++) { create_thread((i + 1) * 10, producer); }
    for (int i = 0; i < c; i++) { thread = create_thread(i, consumer);   }
    semup(scr, -1, "scr");

    // makes the main function wait forever
    pthread_join(thread, NULL);
    return 0;
}

// ==================================================
//
//  Auxiliary
//
// ==================================================

static void signal_(int id) {
    if (tracker[nextfree] == 0 && dp > 0) {
        dp--;
        semup(sp, id, "s-sp");
    } else {
        for (int i = 0; i < c; i++) {
            if (tracker[nextdata[i]] > 0 && id != i && dc[i] > 0) {
                dc[i]--;
                semup(sc[i], id, "s-sc");
                goto END;
            }
        }
        semup(scr, id, "s-scr");
        END:;
    }
}

static pthread_t create_thread(int id, void*(function)(void*)) {
    int* pointer;
    MALLOC(pointer, int);
    *pointer = id;
    pthread_t thread;
    pthread_create(&thread, NULL, function, (void*)pointer);
    printf("Created thread %d...\n", id);
    return thread;
}

static void print_array(int array[], int size) {
    printf("[");
    for (int i = 0; i < size - 1; i++) {
        printf("%d, ", array[i]);
    }
    printf("%d]", array[size - 1]);
}

static void print_buffer_tracker(void) {
    printf("\t\t");
    print_array(buffer, SIZE);
    printf("\t");
    print_array(tracker, SIZE);
    printf("\n");
}
