module SistemaDeArquivos

// ----------------------- Objects ---------------------
// Objeto pode ser  um arquivo ou um diretorio.
// Um diretório pode ser um root ou um diretorio qualquer
abstract sig Object{
	//permission: one Permission
}

sig Archive extends Object{}

abstract sig Directory extends Object{
	directories: set Directory,
	archives: set Archive
}

one sig Root extends Directory{}
sig CommonDirectory extends Directory{}

// ------------------- Permissions ------------------
// Permissões de usuario podem ser Leitura, Leitura e Escrita, ou Dono

abstract sig Permission{}
sig Read in Permission{}
sig Write in Read{}
sig Admin in Write{}

// ------------------------ Users -----------------------
// Usuário é uma entidade do sistema que pode ser Usuario externo, Usuario local ou simplismente um Usuário arbitrário
sig User{
	permission: one Permission
}
sig ExternUser extends User{}
sig LocalUser extends User{}


// -------------------------- Facts --------------------------

//Todo diretório comum tem como ansestral um diretório root
fact SameDirectoryInRoot{
	all d:CommonDirectory | one r: Root | d.~directories = r
}

//Todo diretório comum está relacionado a um unico diretório
fact AllCommonDirectoriesHaveParentDirectory{
	all d:CommonDirectory | one dp: Directory | d.~directories = dp 
} 

// Diretório root não possui um pai
fact RootNotHaveParents {
	all r: Root | #(r.~directories) = 0
}

//Todo diretório não pode conter ele mesmo
fact DirectoryNoContainsHimself{
	all d:Directory | directoryNoContainsHimself[d]
}

pred directoryNoContainsHimself[d:Directory]{
	#(d.directories & d) = 0
}

// Todo arquivo tem somente um diretoro como pai
fact AllArchivesHaveOnlyParentDirectory{
	all a: Archive | one d: Directory | a in d.archives
}

// Diretorio não pode conter seu pai ou um de seus ansestrais
fact DirectoryChildNoConteinsParents{
	all dParent:Directory | all d:Directory | (#(dParent.directories & d) = 1) => (dParent.^directories != d)
}


pred show[]{
}
run show for 20

