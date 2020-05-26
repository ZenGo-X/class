#include <stdlib.h>
#include <mpi.h>

int main()
{
  int pari_MPI_size, pari_MPI_rank;
  int res = MPI_Init(0, NULL);
  if (res == MPI_SUCCESS)
  {
    MPI_Comm_size(MPI_COMM_WORLD, &pari_MPI_size);
    MPI_Comm_rank(MPI_COMM_WORLD, &pari_MPI_rank);
  }
}
