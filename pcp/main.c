#include <assert.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include <unistd.h>

#define seminit(s, n, v) { sem_unlink(n); s = sem_open(n, O_CREAT, 0644, v); }
#define semdown(s, i, n) { sem_wait(s); /*printf("ID %d got %s\n"     , i, n); */}
#define semup(s, i, n)   { sem_post(s); /*printf("ID %d released %s\n", i, n); */}

#define MALLOC(x, t)          x = (t*)malloc(sizeof(t));     if (!x) exit(1);
#define MALLOC_ARRAY(x, t, n) x = (t*)malloc(n * sizeof(t)); if (!x) exit(1);

#define SIZE 10             // size of the buffer

static int P, C;            // number of consumers and producers

static int buffer[SIZE];     // the bounded buffer
static int nextfree = 0;     // TODO
static int nextdata = 0;     // TODO
static int freeslots = SIZE; // TODO

static int dp = 0;          // producer condition counter
static int dc = 0;          // consumer condition counter
static sem_t* sp;           // producer semaphore
static sem_t* sc;           // consumer semaphore
static sem_t* scr;          // critical region semaphore

static pthread_t create_thread(int id, void*(function)(void*));
static void print_buffer(void);

static void* producer(void* id_pointer) {
    int id = *((int*)id_pointer);
    free(id_pointer);

    int data;

    while (true) {
        data = rand() % 100;

        // <await (freeslots > 0);
        // buffer[nextfree] = data;
        // nextfree = (nextfree + 1) % SIZE;
        // freeslots--;>

        semdown(scr, id, "scr");
        if (!(freeslots > 0)) {
            dp++;
            semup(scr, id, "scr");
            semdown(sp, id, "sp");
        }

        buffer[nextfree] = data;

        printf("ID %d produced %d for index %d\t\t", id, data, nextfree);
        print_buffer();

        nextfree = (nextfree + 1) % SIZE;
        freeslots--;

        // printf("nextfree = %d, freeslots = %d\n", nextfree, freeslots);

        // signal
        if (freeslots > 0 && dp > 0) {
            dp--;
            semup(sp, id, "sp");
        } else if (freeslots < SIZE && dc > 0) {
            dc--;
            semup(sc, id, "sc");
        } else {
            semup(scr, id, "scr");
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
        // <await (freeslots < SIZE)
        // data = buffer[nextdata];
        // nextdata = (nextdata + 1) % SIZE;
        // freeslots++;>

        semdown(scr, id, "scr");
        if (!(freeslots < SIZE)) {
            dc++;
            semup(scr, id, "scr");
            semdown(sc, id, "sc");
        }

        data = buffer[nextdata];
        buffer[nextdata] = 0;
        printf("ID %d consumed %d from index %d\t\t", id, data, nextdata);
        print_buffer();
        nextdata = (nextdata + 1) % SIZE;
        freeslots++;

        // signal
        if (freeslots > 0 && dp > 0) {
            dp--;
            semup(sp, id, "sp");
        } else if (freeslots < SIZE && dc > 0) {
            dc--;
            semup(sc, id, "sc");
        } else {
            semup(scr, id, "scr");
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
    seminit(sp , "/sem-producer", 0);
    seminit(sc , "/sem-consumer", 0);
    seminit(scr, "/sem-cr"      , 1);

    // creates threads
    semdown(scr, -1, "scr");
    pthread_t thread;
    for (int i = 0; i < P; i++) { thread = create_thread(i * 10, producer); }
    for (int i = 0; i < C; i++) { thread = create_thread(i, consumer);      }
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

static pthread_t create_thread(int id, void*(function)(void*)) {
    int* pointer;
    MALLOC(pointer, int);
    *pointer = id;
    pthread_t thread;
    pthread_create(&thread, NULL, function, (void*)pointer);
    printf("Created a thread...\n");
    return thread;
}

static void print_buffer(void) {
    printf("[");
    for (int i = 0; i < SIZE - 1; i++) printf("%d, ", buffer[i]);
    printf("%d]\n", buffer[SIZE - 1]);
}
